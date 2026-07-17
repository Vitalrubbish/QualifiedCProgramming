Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Lia.
From AUXLib Require Import int_auto.
From SimpleC.SL Require Import Mem SeparationLogic.
From GraphLib Require Import reachable_basic.
Import ListNotations.
Local Open Scope Z_scope.

From SimpleC.EE.QCP_demos_LLM Require Import kosaraju_rel_lib.

(* ================================================================ *)
(* 2SAT → Implication Graph: Vertex Encoding (pure Z-level)         *)
(*                                                                   *)
(* Variable v (1-indexed, 1 <= v <= n) → two literals:               *)
(*   vertex 2*(v-1)   = literal (v, true)                           *)
(*   vertex 2*(v-1)+1 = literal (v, false)                          *)
(*                                                                   *)
(* C int literal encoding:                                           *)
(*   a > 0  →  (a, true)   →  vertex 2*(a-1)                       *)
(*   a < 0  →  (-a, false) →  vertex 2*(-a-1)+1                    *)
(*                                                                   *)
(* Key invariant: neg_vertex(a) = lit_to_vertex(a) XOR 1             *)
(* ================================================================ *)

Definition lit_to_vertex (a : Z) : Z :=
  2 * (Z.abs a - 1) + (if Z.ltb a 0 then 1 else 0).

Definition neg_vertex (a : Z) : Z :=
  lit_to_vertex (-a).

Lemma lit_to_vertex_range : forall a n,
  1 <= Z.abs a <= n -> 0 <= lit_to_vertex a < 2 * n.
Proof.
  intros a n H. destruct H as [Hlow Hhigh].
  unfold lit_to_vertex.
  case (Z.ltb_spec a 0); intros Hlt.
  - (* a < 0 *)
    assert (Ha : Z.abs a = -a) by (apply Z.abs_neq; lia).
    rewrite Ha. simpl Z.ltb. lia.
  - (* 0 <= a *)
    assert (Ha : Z.abs a = a) by (apply Z.abs_eq; lia).
    rewrite Ha. simpl Z.ltb. lia.
Qed.

Lemma neg_vertex_flip : forall a,
  a <> 0 ->
  neg_vertex a = lit_to_vertex a + (if Z.ltb a 0 then -1 else 1).
Proof.
  intros a Hnz. unfold neg_vertex, lit_to_vertex.
  rewrite Z.abs_opp.
  destruct (Z.ltb a 0) eqn:Hlt; destruct (Z.ltb (-a) 0) eqn:Hlt'; rewrite ?Hlt, ?Hlt'.
  - apply Z.ltb_lt in Hlt. apply Z.ltb_lt in Hlt'. exfalso; lia.
  - apply Z.ltb_lt in Hlt. apply Z.ltb_ge in Hlt'. rewrite Z.abs_neq by lia. lia.
  - apply Z.ltb_ge in Hlt. apply Z.ltb_lt in Hlt'. rewrite Z.abs_eq by lia. lia.
  - apply Z.ltb_ge in Hlt. apply Z.ltb_ge in Hlt'. exfalso; subst; lia.
Qed.

Lemma neg_vertex_distinct : forall a,
  a <> 0 ->
  lit_to_vertex a <> neg_vertex a.
Proof.
  intros a Hnz. rewrite neg_vertex_flip by assumption.
  destruct (Z.ltb a 0); lia.
Qed.


Definition vertex_to_var (u : Z) : Z :=
  u / 2 + 1.

Definition vertex_to_sign (u : Z) : bool :=
  Z.odd u.

Lemma lit_to_vertex_inv : forall a,
  a <> 0 ->
  let u := lit_to_vertex a in
  vertex_to_var u = Z.abs a /\
  (vertex_to_sign u = false <-> 0 < a) /\
  (vertex_to_sign u = true <-> a < 0).
Proof.
  intros a Hnz u. subst u.
  unfold lit_to_vertex, vertex_to_var, vertex_to_sign.
  destruct (Z.ltb a 0) eqn:Hltb.
  - pose proof (proj1 (Z.ltb_lt a 0) Hltb) as Hlt.
    rewrite Z.abs_neq by lia.
    cbv iota.
    replace (Z.odd (2 * (-a - 1) + 1)) with true
      by (rewrite Z.add_comm; rewrite Z.odd_add_mul_even with (n := 1) (m := 2) (p := (-a - 1)); [reflexivity | exists 1; ring]).
    split; [|split].
    + assert (hq : (2 * (-a - 1) + 1) / 2 = (-a - 1)).
      { symmetry. apply (Z.div_unique (2 * (-a - 1) + 1) 2 (-a - 1) 1); [left; split; lia | ring]. }
      rewrite hq; ring.
    + split; [lia | intros; exfalso; lia].
    + split; [auto | intros; auto].
  - pose proof (proj1 (Z.ltb_ge a 0) Hltb) as Hge.
    rewrite Z.abs_eq by lia.
    cbv iota. rewrite Z.add_0_r. rewrite Z.odd_mul, Z.odd_2. rewrite andb_false_l.
    split; [|split].
    + assert (hq : (2 * (a - 1)) / 2 = (a - 1)).
      { symmetry. apply (Z.div_unique (2 * (a - 1)) 2 (a - 1) 0); [left; split; lia | ring]. }
      rewrite hq; ring.
    + split; [lia | intros; auto].
    + split; [lia | intros; exfalso; lia].
Qed.

(* ================================================================ *)
(* CSR well-formedness for 2SAT implication graph (2*n vertices)    *)
(* ================================================================ *)

Definition twosat_csr_wf
  (n : Z) (fadj_col_l fadj_row_l radj_col_l radj_row_l : list Z) : Prop :=
  let num_verts := 2 * n in
  Zlength fadj_row_l = num_verts + 1 /\
  Zlength radj_row_l = num_verts + 1 /\
  m_of fadj_row_l = Zlength fadj_col_l /\
  m_of radj_row_l = Zlength radj_col_l /\
  m_of fadj_row_l = m_of radj_row_l /\
  (forall u, 0 <= u < num_verts -> 0 <= csr_lo u fadj_row_l) /\
  (forall u, 0 <= u < num_verts -> csr_hi u fadj_row_l <= m_of fadj_row_l) /\
  (forall u, 0 <= u < num_verts -> 0 <= csr_lo u radj_row_l) /\
  (forall u, 0 <= u < num_verts -> csr_hi u radj_row_l <= m_of radj_row_l) /\
  (forall j, 0 <= j < m_of fadj_row_l ->
    0 <= Znth j fadj_col_l 0 < num_verts) /\
  (forall j, 0 <= j < m_of radj_row_l ->
    0 <= Znth j radj_col_l 0 < num_verts) /\
  (forall u, 0 <= u < num_verts ->
    csr_lo u fadj_row_l <= csr_hi u fadj_row_l) /\
  (forall u, 0 <= u < num_verts ->
    csr_lo u radj_row_l <= csr_hi u radj_row_l) /\
  (forall u, 0 <= u < num_verts - 1 ->
    csr_hi u fadj_row_l <= csr_hi (u + 1) fadj_row_l) /\
  (forall u, 0 <= u < num_verts - 1 ->
    csr_hi u radj_row_l <= csr_hi (u + 1) radj_row_l).

(* A clause (a \/ b) contributes the two usual implications.  These
   predicates describe the mathematical edge relation only; they do not
   encode the order in which the C cursor loop writes the CSR cells. *)
Definition twosat_clause_forward (a b u v : Z) : Prop :=
  (u = neg_vertex a /\ v = lit_to_vertex b) \/
  (u = neg_vertex b /\ v = lit_to_vertex a).

Definition twosat_clause_reverse (a b u v : Z) : Prop :=
  twosat_clause_forward a b v u.

(* Exact relationship between the six local integers used by the C clause
   loop and the mathematical literal encoding.  This is a pure semantic
   fact, independent of CSR cursor updates; the edge predicates above remain
   the satisfiable implication-graph facts. *)
Definition twosat_clause_encoding
  (a b na nb va vb : Z) : Prop :=
  na = neg_vertex a /\
  nb = neg_vertex b /\
  va = lit_to_vertex a /\
  vb = lit_to_vertex b.

(* Mathematical multiplicities used by the counting pass.  They describe
   which clauses contribute to a row; they do not describe the C loop state. *)
Definition twosat_fdegree (i : Z) (lit1_l lit2_l : list Z) (u : Z) : Z :=
  Zlength (filter (fun a => Z.eqb (neg_vertex a) u)
                   (firstn (Z.to_nat i) lit1_l)) +
  Zlength (filter (fun b => Z.eqb (neg_vertex b) u)
                   (firstn (Z.to_nat i) lit2_l)).

Definition twosat_rdegree (i : Z) (lit1_l lit2_l : list Z) (u : Z) : Z :=
  Zlength (filter (fun b => Z.eqb (lit_to_vertex b) u)
                   (firstn (Z.to_nat i) lit2_l)) +
  Zlength (filter (fun a => Z.eqb (lit_to_vertex a) u)
                   (firstn (Z.to_nat i) lit1_l)).

Definition twosat_degree_prefix
  (n m i : Z) (lit1_l lit2_l fadj_row_l radj_row_l : list Z) : Prop :=
  0 <= i /\ i <= m /\
  Znth 0 fadj_row_l 0 = 0 /\ Znth 0 radj_row_l 0 = 0 /\
  (forall u, 0 <= u < 2 * n ->
    Znth (u + 1) fadj_row_l 0 = twosat_fdegree i lit1_l lit2_l u /\
    Znth (u + 1) radj_row_l 0 = twosat_rdegree i lit1_l lit2_l u).

Fixpoint twosat_sum (l : list Z) : Z :=
  match l with
  | nil => 0
  | x :: xs => x + twosat_sum xs
  end.

Definition twosat_fdegree_sum
  (m : Z) (lit1_l lit2_l : list Z) (u : Z) : Z :=
  twosat_sum
    (map (fun v => twosat_fdegree m lit1_l lit2_l v)
         (map Z.of_nat (seq 0 (Z.to_nat u)))).

Definition twosat_rdegree_sum
  (m : Z) (lit1_l lit2_l : list Z) (u : Z) : Z :=
  twosat_sum
    (map (fun v => twosat_rdegree m lit1_l lit2_l v)
         (map Z.of_nat (seq 0 (Z.to_nat u)))).

(* At prefix-loop index i, rows at and before i are cumulative degree sums;
   the untouched suffix still contains the individual degree entries. *)
Definition twosat_rows_prefix_step
  (n m i : Z) (lit1_l lit2_l fadj_row_l radj_row_l : list Z) : Prop :=
  0 <= i /\ i <= 2 * n /\
  (forall u, 0 <= u <= 2 * n ->
    (u <= i ->
      Znth u fadj_row_l 0 = twosat_fdegree_sum m lit1_l lit2_l u /\
      Znth u radj_row_l 0 = twosat_rdegree_sum m lit1_l lit2_l u) /\
    (i < u ->
      Znth u fadj_row_l 0 = twosat_fdegree m lit1_l lit2_l (u - 1) /\
      Znth u radj_row_l 0 = twosat_rdegree m lit1_l lit2_l (u - 1))).

Definition twosat_prefix_edge
  (i : Z) (lit1_l lit2_l : list Z) (u v : Z) : Prop :=
  exists k, 0 <= k /\ k < i /\
    twosat_clause_forward (Znth k lit1_l 0) (Znth k lit2_l 0) u v.

Definition twosat_prefix_reverse_edge
  (i : Z) (lit1_l lit2_l : list Z) (u v : Z) : Prop :=
  exists k, 0 <= k /\ k < i /\
    twosat_clause_reverse (Znth k lit1_l 0) (Znth k lit2_l 0) u v.

(* The cursor relation is a semantic prefix relation: every cell before a
   cursor belongs to the prefix edge relation, and the prefix edge relation
   is represented exactly by those cells.  It is intentionally independent
   of the C update expression used to advance the cursor. *)
Definition twosat_cursor_bounds
  (n : Z) (fadj_row_l radj_row_l fcur_l rcur_l : list Z) : Prop :=
  let num_verts := 2 * n in
  Zlength fcur_l = num_verts + 1 /\
  Zlength rcur_l = num_verts + 1 /\
  (forall u, 0 <= u < num_verts ->
    csr_lo u fadj_row_l <= Znth u fcur_l 0 /\
    Znth u fcur_l 0 <= csr_hi u fadj_row_l) /\
  (forall u, 0 <= u < num_verts ->
    csr_lo u radj_row_l <= Znth u rcur_l 0 /\
    Znth u rcur_l 0 <= csr_hi u radj_row_l).

(* The cursors describe the exact number of edge instances contributed by
   the processed clause prefix, not merely an arbitrary position inside the
   row.  This remains meaningful when two edge instances have the same
   source or destination row, as in (x \/ x). *)
Definition twosat_cursor_occupancy
  (n m i : Z) (lit1_l lit2_l fadj_row_l radj_row_l fcur_l rcur_l : list Z) : Prop :=
  0 <= i /\ i <= m /\
  Zlength fcur_l = 2 * n + 1 /\ Zlength rcur_l = 2 * n + 1 /\
  (forall u, 0 <= u < 2 * n ->
    Znth u fcur_l 0 = csr_lo u fadj_row_l + twosat_fdegree i lit1_l lit2_l u /\
    Znth u rcur_l 0 = csr_lo u radj_row_l + twosat_rdegree i lit1_l lit2_l u).

(* The completed row arrays contain the full prefix degree at every row end. *)
Definition twosat_rows_degree_consistent
  (n m : Z) (lit1_l lit2_l fadj_row_l radj_row_l : list Z) : Prop :=
  Zlength fadj_row_l = 2 * n + 1 /\ Zlength radj_row_l = 2 * n + 1 /\
  (forall u, 0 <= u < 2 * n ->
    csr_hi u fadj_row_l = csr_lo u fadj_row_l + twosat_fdegree m lit1_l lit2_l u /\
    csr_hi u radj_row_l = csr_lo u radj_row_l + twosat_rdegree m lit1_l lit2_l u).

Definition twosat_prefix_csr_faithful
  (n i : Z) (lit1_l lit2_l fadj_col_l fadj_row_l fcur_l : list Z) : Prop :=
  forall u v, 0 <= u < 2 * n -> 0 <= v < 2 * n ->
    twosat_prefix_edge i lit1_l lit2_l u v <->
    exists j, csr_lo u fadj_row_l <= j /\
      j < Znth u fcur_l 0 /\ Znth j fadj_col_l 0 = v.

Definition twosat_prefix_reverse_csr_faithful
  (n i : Z) (lit1_l lit2_l radj_col_l radj_row_l rcur_l : list Z) : Prop :=
  forall u v, 0 <= u < 2 * n -> 0 <= v < 2 * n ->
    twosat_prefix_reverse_edge i lit1_l lit2_l u v <->
    exists j, csr_lo u radj_row_l <= j /\
      j < Znth u rcur_l 0 /\ Znth j radj_col_l 0 = v.

Definition twosat_processed_prefix
  (n m i : Z) (lit1_l lit2_l fadj_col_l fadj_row_l
               radj_col_l radj_row_l fcur_l rcur_l : list Z) : Prop :=
  0 <= i /\ i <= m /\
  Zlength lit1_l = m /\ Zlength lit2_l = m /\
  twosat_cursor_bounds n fadj_row_l radj_row_l fcur_l rcur_l /\
  twosat_rows_degree_consistent n m lit1_l lit2_l fadj_row_l radj_row_l /\
  twosat_cursor_occupancy n m i lit1_l lit2_l
    fadj_row_l radj_row_l fcur_l rcur_l /\
  twosat_prefix_csr_faithful n i lit1_l lit2_l
    fadj_col_l fadj_row_l fcur_l /\
  twosat_prefix_reverse_csr_faithful n i lit1_l lit2_l
    radj_col_l radj_row_l rcur_l.

Definition twosat_processed_complete
  (n m : Z) (lit1_l lit2_l fadj_col_l fadj_row_l
             radj_col_l radj_row_l fcur_l rcur_l : list Z) : Prop :=
  twosat_processed_prefix n m m lit1_l lit2_l
    fadj_col_l fadj_row_l radj_col_l radj_row_l fcur_l rcur_l /\
  twosat_cursor_bounds n fadj_row_l radj_row_l fcur_l rcur_l /\
  twosat_rows_degree_consistent n m lit1_l lit2_l fadj_row_l radj_row_l /\
  (forall u, 0 <= u < 2 * n ->
    Znth u fcur_l 0 = csr_hi u fadj_row_l /\
    Znth u rcur_l 0 = csr_hi u radj_row_l) /\
  twosat_prefix_csr_faithful n m lit1_l lit2_l
    fadj_col_l fadj_row_l fcur_l /\
  twosat_prefix_reverse_csr_faithful n m lit1_l lit2_l
    radj_col_l radj_row_l rcur_l.

Definition twosat_graph_edges
  (n m : Z) (lit1_l lit2_l : list Z) (g : AdjGraph) : Prop :=
  forall u v, 0 <= u < 2 * n -> 0 <= v < 2 * n ->
    In v (nth (Z.to_nat u) (adj_fwd g) nil) <->
      exists k, 0 <= k /\ k < m /\
        twosat_clause_forward (Znth k lit1_l 0) (Znth k lit2_l 0) u v.

(* Guarded graph validity for this Z-indexed case.  The shared graph
   predicate quantifies its converse law over arbitrary integers; that is
   incompatible with Z.to_nat on negative indices, so this case uses the
   mathematically relevant valid-vertex restriction explicitly. *)
Definition twosat_adj_graph_valid (g : AdjGraph) : Prop :=
  Zlength (adj_fwd g) = adj_verts g /\
  Zlength (adj_rev g) = adj_verts g /\
  (forall u, 0 <= u < adj_verts g ->
    forall v, In v (nth (Z.to_nat u) (adj_fwd g) nil) ->
      0 <= v < adj_verts g) /\
  (forall u, 0 <= u < adj_verts g ->
    forall v, In v (nth (Z.to_nat u) (adj_rev g) nil) ->
      0 <= v < adj_verts g) /\
  (forall u v, 0 <= u < adj_verts g -> 0 <= v < adj_verts g ->
    In v (nth (Z.to_nat u) (adj_fwd g) nil) <->
    In u (nth (Z.to_nat v) (adj_rev g) nil)).

(* Complete graph correctness: CSR shape and bounds, exact clause-induced
   abstract adjacency, and the mutual forward/reverse CSR correspondence. *)
Definition twosat_kosaraju_graph
  (n m : Z) (lit1_l lit2_l fadj_col_l fadj_row_l
             radj_col_l radj_row_l : list Z) : Prop :=
  twosat_csr_wf n fadj_col_l fadj_row_l radj_col_l radj_row_l /\
  Zlength lit1_l = m /\ Zlength lit2_l = m /\
  exists (g : AdjGraph),
    adj_verts g = 2 * n /\
    twosat_adj_graph_valid g /\
    twosat_graph_edges n m lit1_l lit2_l g /\
    csr2_faithful g fadj_col_l fadj_row_l /\
    csr1_faithful g radj_col_l radj_row_l.

(* ================================================================ *)
(* Canonical clause-induced adjacency graph.  These definitions enumerate
   mathematical edge instances and do not mirror the C cursor algorithm. *)

Definition twosat_vertices (n : Z) : list Z :=
  map Z.of_nat (seq 0 (Z.to_nat (2 * n))).

Definition twosat_clause_forward_row (a b u : Z) : list Z :=
  (if Z.eqb u (neg_vertex a) then [lit_to_vertex b] else []) ++
  (if Z.eqb u (neg_vertex b) then [lit_to_vertex a] else []).

Definition twosat_clause_reverse_row (a b v : Z) : list Z :=
  (if Z.eqb v (lit_to_vertex b) then [neg_vertex a] else []) ++
  (if Z.eqb v (lit_to_vertex a) then [neg_vertex b] else []).

Definition twosat_forward_row
  (m : Z) (lit1_l lit2_l : list Z) (u : Z) : list Z :=
  flat_map
    (fun k =>
       twosat_clause_forward_row
         (Znth (Z.of_nat k) lit1_l 0)
         (Znth (Z.of_nat k) lit2_l 0) u)
    (seq 0 (Z.to_nat m)).

Definition twosat_reverse_row
  (m : Z) (lit1_l lit2_l : list Z) (v : Z) : list Z :=
  flat_map
    (fun k =>
       twosat_clause_reverse_row
         (Znth (Z.of_nat k) lit1_l 0)
         (Znth (Z.of_nat k) lit2_l 0) v)
    (seq 0 (Z.to_nat m)).

Definition twosat_canonical_graph
  (n m : Z) (lit1_l lit2_l : list Z) : AdjGraph :=
  {| adj_verts := 2 * n;
     adj_fwd := map (twosat_forward_row m lit1_l lit2_l) (twosat_vertices n);
     adj_rev := map (twosat_reverse_row m lit1_l lit2_l) (twosat_vertices n) |}.

Definition twosat_clause_input_wf
  (n m : Z) (lit1_l lit2_l : list Z) : Prop :=
  0 <= n /\ 0 <= m /\
  Zlength lit1_l = m /\ Zlength lit2_l = m /\
  (forall k, 0 <= k < m ->
     1 <= Z.abs (Znth k lit1_l 0) <= n /\
     1 <= Z.abs (Znth k lit2_l 0) <= n).

Definition twosat_full_csr_shape
  (n : Z) (fadj_col_l fadj_row_l radj_col_l radj_row_l : list Z) : Prop :=
  twosat_csr_wf n fadj_col_l fadj_row_l radj_col_l radj_row_l.

Lemma twosat_clause_forward_row_reverse :
  forall a b u v,
    In v (twosat_clause_forward_row a b u) <->
    In u (twosat_clause_reverse_row a b v).
Proof.
  intros a b u v.
  unfold twosat_clause_forward_row, twosat_clause_reverse_row.
  repeat rewrite in_app_iff.
  destruct (Z.eqb u (neg_vertex a)) eqn:Hua;
  destruct (Z.eqb u (neg_vertex b)) eqn:Hub;
  destruct (Z.eqb v (lit_to_vertex b)) eqn:Hvb;
  destruct (Z.eqb v (lit_to_vertex a)) eqn:Hva;
  simpl in *;
  repeat match goal with
  | H : Z.eqb _ _ = true |- _ => apply Z.eqb_eq in H
  | H : Z.eqb _ _ = false |- _ => apply Z.eqb_neq in H
  end;
  try (intuition congruence).
Qed.

Lemma twosat_clause_forward_row_spec :
  forall a b u v,
    In v (twosat_clause_forward_row a b u) <->
    twosat_clause_forward a b u v.
Proof.
  intros a b u v.
  unfold twosat_clause_forward_row, twosat_clause_forward.
  repeat rewrite in_app_iff.
  destruct (Z.eqb u (neg_vertex a)) eqn:Hua;
  destruct (Z.eqb u (neg_vertex b)) eqn:Hub;
  simpl;
  repeat match goal with
  | H : Z.eqb _ _ = true |- _ => apply Z.eqb_eq in H
  | H : Z.eqb _ _ = false |- _ => apply Z.eqb_neq in H
  end;
  simpl in *; try (intuition congruence).
Qed.

Lemma twosat_clause_reverse_row_spec :
  forall a b u v,
    In v (twosat_clause_reverse_row a b u) <->
    twosat_clause_reverse a b u v.
Proof.
  intros a b u v.
  unfold twosat_clause_reverse.
  split; intro H.
  - apply (proj1 (twosat_clause_forward_row_spec a b v u)).
    apply (proj2 (twosat_clause_forward_row_reverse a b v u)).
    exact H.
  - apply (proj1 (twosat_clause_forward_row_reverse a b v u)).
    apply (proj2 (twosat_clause_forward_row_spec a b v u)).
    exact H.
Qed.

Lemma twosat_clause_forward_row_valid :
  forall n a b u v,
    1 <= Z.abs a <= n ->
    1 <= Z.abs b <= n ->
    In v (twosat_clause_forward_row a b u) ->
    0 <= v < 2 * n.
Proof.
  intros n a b u v Ha Hb Hin.
  unfold twosat_clause_forward_row in Hin.
  rewrite in_app_iff in Hin.
  destruct (Z.eqb u (neg_vertex a)) eqn:Ea.
  - destruct (Z.eqb u (neg_vertex b)) eqn:Eb.
    + simpl in Hin. destruct Hin as [Hin | Hin].
      * assert (Heq : lit_to_vertex b = v) by (simpl in Hin; tauto).
        rewrite <- Heq. apply lit_to_vertex_range; exact Hb.
      * assert (Heq : lit_to_vertex a = v) by (simpl in Hin; tauto).
        rewrite <- Heq. apply lit_to_vertex_range; exact Ha.
    + simpl in Hin. destruct Hin as [Hin | Hin].
      * assert (Heq : lit_to_vertex b = v) by (simpl in Hin; tauto).
        rewrite <- Heq. apply lit_to_vertex_range; exact Hb.
      * simpl in Hin; tauto.
  - destruct (Z.eqb u (neg_vertex b)) eqn:Eb.
    + simpl in Hin. destruct Hin as [Hin | Hin].
      * simpl in Hin; tauto.
      * assert (Heq : lit_to_vertex a = v) by (simpl in Hin; tauto).
        rewrite <- Heq. apply lit_to_vertex_range; exact Ha.
    + simpl in Hin; tauto.
Qed.

Lemma twosat_neg_vertex_range :
  forall n a, 1 <= Z.abs a <= n -> 0 <= neg_vertex a < 2 * n.
Proof.
  intros n a Ha.
  unfold neg_vertex.
  apply lit_to_vertex_range.
  rewrite Z.abs_opp.
  exact Ha.
Qed.

Lemma twosat_clause_reverse_row_valid :
  forall n a b u v,
    1 <= Z.abs a <= n ->
    1 <= Z.abs b <= n ->
    In v (twosat_clause_reverse_row a b u) ->
    0 <= v < 2 * n.
Proof.
  intros n a b u v Ha Hb Hin.
  unfold twosat_clause_reverse_row in Hin.
  rewrite in_app_iff in Hin.
  destruct (Z.eqb u (lit_to_vertex b)) eqn:Eb.
  - destruct (Z.eqb u (lit_to_vertex a)) eqn:Ea.
    + simpl in Hin. destruct Hin as [Hin | Hin].
      * assert (Heq : neg_vertex a = v) by (simpl in Hin; tauto).
        rewrite <- Heq. apply twosat_neg_vertex_range; exact Ha.
      * assert (Heq : neg_vertex b = v) by (simpl in Hin; tauto).
        rewrite <- Heq. apply twosat_neg_vertex_range; exact Hb.
    + simpl in Hin. destruct Hin as [Hin | Hin].
      * assert (Heq : neg_vertex a = v) by (simpl in Hin; tauto).
        rewrite <- Heq. apply twosat_neg_vertex_range; exact Ha.
      * simpl in Hin; tauto.
  - destruct (Z.eqb u (lit_to_vertex a)) eqn:Ea.
    + simpl in Hin. destruct Hin as [Hin | Hin].
      * simpl in Hin; tauto.
      * assert (Heq : neg_vertex b = v) by (simpl in Hin; tauto).
        rewrite <- Heq. apply twosat_neg_vertex_range; exact Hb.
    + simpl in Hin; tauto.
Qed.

Lemma twosat_forward_row_reverse :
  forall m lit1_l lit2_l u v,
    In v (twosat_forward_row m lit1_l lit2_l u) <->
    In u (twosat_reverse_row m lit1_l lit2_l v).
Proof.
  intros m lit1_l lit2_l u v.
  unfold twosat_forward_row, twosat_reverse_row.
  rewrite !in_flat_map.
  split; intros H.
  - destruct H as [k [Hk Hv]].
    exists k. split; [exact Hk|].
    apply (proj1 (twosat_clause_forward_row_reverse
      (Znth (Z.of_nat k) lit1_l 0)
      (Znth (Z.of_nat k) lit2_l 0) u v)).
    exact Hv.
  - destruct H as [k [Hk Hu]].
    exists k. split; [exact Hk|].
    apply (proj2 (twosat_clause_forward_row_reverse
      (Znth (Z.of_nat k) lit1_l 0)
      (Znth (Z.of_nat k) lit2_l 0) u v)).
    exact Hu.
Qed.

Lemma nth_map_default_valid :
  forall (A B : Type) (f : A -> B) (l : list A) (d : B) (a : A) (i : nat),
    (i < length l)%nat -> nth i (map f l) d = f (nth i l a).
Proof.
  intros A B f l.
  induction l as [|x xs IH]; intros d a i Hi.
  - simpl in Hi. lia.
  - destruct i as [|i].
    + reflexivity.
    + simpl in Hi. apply IH. lia.
Qed.

Lemma twosat_vertices_length :
  forall n, 0 <= n -> Zlength (twosat_vertices n) = 2 * n.
Proof.
  intros n Hn.
  unfold twosat_vertices.
  rewrite Zlength_correct, length_map, length_seq.
  rewrite Z2Nat.id by lia.
  reflexivity.
Qed.

Lemma twosat_vertices_nth :
  forall n u, 0 <= u < 2 * n ->
    nth (Z.to_nat u) (twosat_vertices n) 0 = u.
Proof.
  intros n u Hu.
  unfold twosat_vertices.
  assert (Hnat : (Z.to_nat u < Z.to_nat (2 * n))%nat).
  { apply (proj1 (Z2Nat.inj_lt u (2 * n) (proj1 Hu) ltac:(lia))).
    exact (proj2 Hu). }
  rewrite (@nth_map_default_valid nat Z Z.of_nat
    (seq 0 (Z.to_nat (2 * n))) 0%Z 0%nat (Z.to_nat u)).
  - rewrite (seq_nth 0 0 Hnat).
    simpl. rewrite Z2Nat.id by lia. lia.
  - rewrite length_seq. exact Hnat.
Qed.

Lemma twosat_clause_index_wf :
  forall n m lit1_l lit2_l k,
    twosat_clause_input_wf n m lit1_l lit2_l ->
    In k (seq 0 (Z.to_nat m)) ->
    1 <= Z.abs (Znth (Z.of_nat k) lit1_l 0) <= n /\
    1 <= Z.abs (Znth (Z.of_nat k) lit2_l 0) <= n.
Proof.
  intros n m lit1_l lit2_l k Hw Hk.
  destruct Hw as [_ [Hm [_ [_ Hlit]]]].
  apply in_seq in Hk.
  assert (Hkm : (Z.of_nat k < m)%Z).
  { apply (proj2 (Z2Nat.inj_lt (Z.of_nat k) m ltac:(lia) ltac:(lia))).
    simpl. lia. }
  assert (Hknonneg : (0 <= Z.of_nat k)%Z) by lia.
  exact (Hlit (Z.of_nat k) (conj Hknonneg Hkm)).
Qed.

Lemma twosat_forward_row_valid_input :
  forall n m lit1_l lit2_l u v,
    twosat_clause_input_wf n m lit1_l lit2_l ->
    0 <= u < 2 * n ->
    In v (twosat_forward_row m lit1_l lit2_l u) ->
    0 <= v < 2 * n.
Proof.
  intros n m lit1_l lit2_l u v Hw Hu Hv.
  unfold twosat_forward_row in Hv.
  rewrite in_flat_map in Hv.
  destruct Hv as [k [Hk Hrow]].
  pose proof (twosat_clause_index_wf n m lit1_l lit2_l k Hw Hk) as Hc.
  apply (twosat_clause_forward_row_valid n
    (Znth (Z.of_nat k) lit1_l 0)
    (Znth (Z.of_nat k) lit2_l 0) u v).
  - exact (proj1 Hc).
  - exact (proj2 Hc).
  - exact Hrow.
Qed.

Lemma twosat_reverse_row_valid_input :
  forall n m lit1_l lit2_l u v,
    twosat_clause_input_wf n m lit1_l lit2_l ->
    0 <= u < 2 * n ->
    In v (twosat_reverse_row m lit1_l lit2_l u) ->
    0 <= v < 2 * n.
Proof.
  intros n m lit1_l lit2_l u v Hw Hu Hv.
  unfold twosat_reverse_row in Hv.
  rewrite in_flat_map in Hv.
  destruct Hv as [k [Hk Hrow]].
  pose proof (twosat_clause_index_wf n m lit1_l lit2_l k Hw Hk) as Hc.
  apply (twosat_clause_reverse_row_valid n
    (Znth (Z.of_nat k) lit1_l 0)
    (Znth (Z.of_nat k) lit2_l 0) u v).
  - exact (proj1 Hc).
  - exact (proj2 Hc).
  - exact Hrow.
Qed.

Lemma twosat_canonical_graph_valid :
  forall n m lit1_l lit2_l,
    twosat_clause_input_wf n m lit1_l lit2_l ->
    twosat_adj_graph_valid (twosat_canonical_graph n m lit1_l lit2_l).
Proof.
  intros n m lit1_l lit2_l Hw.
  destruct Hw as [Hn [Hm [Hl1 [Hl2 Hlit]]]].
  unfold twosat_adj_graph_valid, twosat_canonical_graph.
  simpl.
  split.
  { rewrite Zlength_correct, length_map.
    rewrite <- Zlength_correct.
    apply twosat_vertices_length.
    exact Hn. }
  split.
  { rewrite Zlength_correct, length_map.
    rewrite <- Zlength_correct.
    apply twosat_vertices_length.
    exact Hn. }
  split.
  { intros u Hu v Hv.
    assert (Hw : twosat_clause_input_wf n m lit1_l lit2_l).
    { unfold twosat_clause_input_wf.
      split; [exact Hn|]. split; [exact Hm|].
      split; [exact Hl1|]. split; [exact Hl2|]. exact Hlit. }
    assert (Hidx : (Z.to_nat u < Z.to_nat (2 * n))%nat).
    { apply (proj1 (Z2Nat.inj_lt u (2 * n) (proj1 Hu) ltac:(lia))).
      exact (proj2 Hu). }
    assert (Hlen : (Z.to_nat u < length (twosat_vertices n))%nat).
    { unfold twosat_vertices. rewrite length_map, length_seq. exact Hidx. }
    rewrite (@nth_map_default_valid Z (list Z)
      (twosat_forward_row m lit1_l lit2_l)
      (twosat_vertices n) nil 0%Z (Z.to_nat u) Hlen) in Hv.
    rewrite (twosat_vertices_nth n u Hu) in Hv.
    apply twosat_forward_row_valid_input with (m := m)
      (lit1_l := lit1_l) (lit2_l := lit2_l) (u := u).
    - exact Hw.
    - exact Hu.
    - exact Hv. }
  split.
  { intros u Hu v Hv.
    assert (Hw : twosat_clause_input_wf n m lit1_l lit2_l).
    { unfold twosat_clause_input_wf.
      split; [exact Hn|]. split; [exact Hm|].
      split; [exact Hl1|]. split; [exact Hl2|]. exact Hlit. }
    assert (Hidx : (Z.to_nat u < Z.to_nat (2 * n))%nat).
    { apply (proj1 (Z2Nat.inj_lt u (2 * n) (proj1 Hu) ltac:(lia))).
      exact (proj2 Hu). }
    assert (Hlen : (Z.to_nat u < length (twosat_vertices n))%nat).
    { unfold twosat_vertices. rewrite length_map, length_seq. exact Hidx. }
    rewrite (@nth_map_default_valid Z (list Z)
      (twosat_reverse_row m lit1_l lit2_l)
      (twosat_vertices n) nil 0%Z (Z.to_nat u) Hlen) in Hv.
    rewrite (twosat_vertices_nth n u Hu) in Hv.
    apply twosat_reverse_row_valid_input with (m := m)
      (lit1_l := lit1_l) (lit2_l := lit2_l) (u := u).
    - exact Hw.
    - exact Hu.
    - exact Hv. }
  { intros u v Hu Hv.
    assert (HidxU : (Z.to_nat u < Z.to_nat (2 * n))%nat).
    { apply (proj1 (Z2Nat.inj_lt u (2 * n) (proj1 Hu) ltac:(lia))).
      exact (proj2 Hu). }
    assert (HidxV : (Z.to_nat v < Z.to_nat (2 * n))%nat).
    { apply (proj1 (Z2Nat.inj_lt v (2 * n) (proj1 Hv) ltac:(lia))).
      exact (proj2 Hv). }
    assert (HlenU : (Z.to_nat u < length (twosat_vertices n))%nat).
    { unfold twosat_vertices. rewrite length_map, length_seq. exact HidxU. }
    assert (HlenV : (Z.to_nat v < length (twosat_vertices n))%nat).
    { unfold twosat_vertices. rewrite length_map, length_seq. exact HidxV. }
    rewrite (@nth_map_default_valid Z (list Z)
      (twosat_forward_row m lit1_l lit2_l)
      (twosat_vertices n) nil 0%Z (Z.to_nat u) HlenU).
    rewrite (@nth_map_default_valid Z (list Z)
      (twosat_reverse_row m lit1_l lit2_l)
      (twosat_vertices n) nil 0%Z (Z.to_nat v) HlenV).
    rewrite (twosat_vertices_nth n u Hu).
    rewrite (twosat_vertices_nth n v Hv).
    apply twosat_forward_row_reverse. }
Qed.

Lemma twosat_forward_row_membership :
  forall n m lit1_l lit2_l u v,
    twosat_clause_input_wf n m lit1_l lit2_l ->
    In v (twosat_forward_row m lit1_l lit2_l u) <->
      exists k : Z, 0 <= k /\ k < m /\
        twosat_clause_forward (Znth k lit1_l 0) (Znth k lit2_l 0) u v.
Proof.
  intros n m lit1_l lit2_l u v Hw.
  destruct Hw as [Hn [Hm [Hl1 [Hl2 Hlit]]]].
  unfold twosat_forward_row.
  rewrite in_flat_map.
  split.
  - intros [k [Hk Hrow]].
    apply in_seq in Hk.
    exists (Z.of_nat k).
    split; [lia|].
    split.
    + apply (proj2 (Z2Nat.inj_lt (Z.of_nat k) m ltac:(lia) ltac:(lia))).
      rewrite Nat2Z.id. exact (proj2 Hk).
    + apply (proj1 (twosat_clause_forward_row_spec
        (Znth (Z.of_nat k) lit1_l 0)
        (Znth (Z.of_nat k) lit2_l 0) u v)).
      exact Hrow.
  - intros [k [Hk0 [Hkm Hcl]]].
    assert (Hknat : (Z.to_nat k < Z.to_nat m)%nat).
    { apply (proj1 (Z2Nat.inj_lt k m ltac:(lia) ltac:(lia))).
      exact Hkm. }
    exists (Z.to_nat k).
    split.
    + apply in_seq. split; [lia|exact Hknat].
    + apply (proj2 (twosat_clause_forward_row_spec
        (Znth (Z.of_nat (Z.to_nat k)) lit1_l 0)
        (Znth (Z.of_nat (Z.to_nat k)) lit2_l 0) u v)).
      rewrite Z2Nat.id by lia. exact Hcl.
Qed.

Lemma twosat_reverse_row_membership :
  forall n m lit1_l lit2_l u v,
    twosat_clause_input_wf n m lit1_l lit2_l ->
    In v (twosat_reverse_row m lit1_l lit2_l u) <->
      exists k : Z, 0 <= k /\ k < m /\
        twosat_clause_reverse (Znth k lit1_l 0) (Znth k lit2_l 0) u v.
Proof.
  intros n m lit1_l lit2_l u v Hw.
  destruct Hw as [Hn [Hm [Hl1 [Hl2 Hlit]]]].
  unfold twosat_reverse_row.
  rewrite in_flat_map.
  split.
  - intros [k [Hk Hrow]].
    apply in_seq in Hk.
    exists (Z.of_nat k).
    split; [lia|].
    split.
    + apply (proj2 (Z2Nat.inj_lt (Z.of_nat k) m ltac:(lia) ltac:(lia))).
      rewrite Nat2Z.id. exact (proj2 Hk).
    + apply (proj1 (twosat_clause_reverse_row_spec
        (Znth (Z.of_nat k) lit1_l 0)
        (Znth (Z.of_nat k) lit2_l 0) u v)).
      exact Hrow.
  - intros [k [Hk0 [Hkm Hcl]]].
    assert (Hknat : (Z.to_nat k < Z.to_nat m)%nat).
    { apply (proj1 (Z2Nat.inj_lt k m ltac:(lia) ltac:(lia))).
      exact Hkm. }
    exists (Z.to_nat k).
    split.
    + apply in_seq. split; [lia|exact Hknat].
    + apply (proj2 (twosat_clause_reverse_row_spec
        (Znth (Z.of_nat (Z.to_nat k)) lit1_l 0)
        (Znth (Z.of_nat (Z.to_nat k)) lit2_l 0) u v)).
      rewrite Z2Nat.id by lia. exact Hcl.
Qed.

Lemma twosat_graph_edges_canonical :
  forall n m lit1_l lit2_l,
    twosat_clause_input_wf n m lit1_l lit2_l ->
    twosat_graph_edges n m lit1_l lit2_l
      (twosat_canonical_graph n m lit1_l lit2_l).
Proof.
  intros n m lit1_l lit2_l Hw u v Hu Hv.
  unfold twosat_graph_edges, twosat_canonical_graph.
  simpl.
  assert (Hidx : (Z.to_nat u < Z.to_nat (2 * n))%nat).
  { apply (proj1 (Z2Nat.inj_lt u (2 * n) ltac:(lia) ltac:(lia))).
    exact (proj2 Hu). }
  assert (Hlen : (Z.to_nat u < length (twosat_vertices n))%nat).
  { unfold twosat_vertices. rewrite length_map, length_seq. exact Hidx. }
  rewrite (@nth_map_default_valid Z (list Z)
    (twosat_forward_row m lit1_l lit2_l)
    (twosat_vertices n) nil 0%Z (Z.to_nat u) Hlen).
  rewrite (twosat_vertices_nth n u Hu).
  apply (twosat_forward_row_membership n m lit1_l lit2_l u v); exact Hw.
Qed.

Lemma twosat_step_canonical_forward :
  forall n m lit1_l lit2_l u v,
    twosat_clause_input_wf n m lit1_l lit2_l ->
    0 <= u < 2 * n -> 0 <= v < 2 * n ->
    @step AdjGraph Z (Z * Z) AdjGraph_graph
      (twosat_canonical_graph n m lit1_l lit2_l) u v <->
      In v (twosat_forward_row m lit1_l lit2_l u).
Proof.
  intros n m lit1_l lit2_l u v Hw Hu Hv.
  unfold step.
  split.
  - intros [e He].
    unfold AdjGraph_graph, adj_step_aux in He.
    destruct He as [He [Hxu [Hyv Hrow]]].
    unfold twosat_canonical_graph in Hrow. simpl in Hrow.
    assert (Hidx : (Z.to_nat u < Z.to_nat (2 * n))%nat).
    { apply (proj1 (Z2Nat.inj_lt u (2 * n) ltac:(lia) ltac:(lia))).
      exact (proj2 Hu). }
    assert (Hlen : (Z.to_nat u < length (twosat_vertices n))%nat).
    { unfold twosat_vertices. rewrite length_map, length_seq. exact Hidx. }
    rewrite (@nth_map_default_valid Z (list Z)
      (twosat_forward_row m lit1_l lit2_l)
      (twosat_vertices n) nil 0%Z (Z.to_nat u) Hlen) in Hrow.
    rewrite (twosat_vertices_nth n u Hu) in Hrow.
    exact Hrow.
  - intro Hrow.
    exists (u, v).
    unfold AdjGraph_graph, adj_step_aux.
    split; [reflexivity|]. split; [exact Hu|]. split; [exact Hv|].
    unfold twosat_canonical_graph in *; simpl.
    assert (Hidx : (Z.to_nat u < Z.to_nat (2 * n))%nat).
    { apply (proj1 (Z2Nat.inj_lt u (2 * n) ltac:(lia) ltac:(lia))).
      exact (proj2 Hu). }
    assert (Hlen : (Z.to_nat u < length (twosat_vertices n))%nat).
    { unfold twosat_vertices. rewrite length_map, length_seq. exact Hidx. }
    rewrite (@nth_map_default_valid Z (list Z)
      (twosat_forward_row m lit1_l lit2_l)
      (twosat_vertices n) nil 0%Z (Z.to_nat u) Hlen).
    rewrite (twosat_vertices_nth n u Hu).
    exact Hrow.
Qed.

Lemma twosat_canonical_reverse_row :
  forall n m lit1_l lit2_l u v,
    twosat_clause_input_wf n m lit1_l lit2_l ->
    0 <= u < 2 * n ->
    In v (nth (Z.to_nat u)
      (adj_rev (twosat_canonical_graph n m lit1_l lit2_l)) nil) <->
      exists k : Z, 0 <= k /\ k < m /\
        twosat_clause_reverse (Znth k lit1_l 0) (Znth k lit2_l 0) u v.
Proof.
  intros n m lit1_l lit2_l u v Hw Hu.
  unfold twosat_canonical_graph. simpl.
  assert (Hidx : (Z.to_nat u < Z.to_nat (2 * n))%nat).
  { apply (proj1 (Z2Nat.inj_lt u (2 * n) ltac:(lia) ltac:(lia))).
    exact (proj2 Hu). }
  assert (Hlen : (Z.to_nat u < length (twosat_vertices n))%nat).
  { unfold twosat_vertices. rewrite length_map, length_seq. exact Hidx. }
  rewrite (@nth_map_default_valid Z (list Z)
    (twosat_reverse_row m lit1_l lit2_l)
    (twosat_vertices n) nil 0%Z (Z.to_nat u) Hlen).
  rewrite (twosat_vertices_nth n u Hu).
  apply (twosat_reverse_row_membership n m lit1_l lit2_l u v); exact Hw.
Qed.

Lemma twosat_prefix_edge_full :
  forall n m lit1_l lit2_l u v,
    twosat_clause_input_wf n m lit1_l lit2_l ->
    twosat_prefix_edge m lit1_l lit2_l u v <->
      In v (twosat_forward_row m lit1_l lit2_l u).
Proof.
  intros n m lit1_l lit2_l u v Hw.
  unfold twosat_prefix_edge. symmetry.
  apply (twosat_forward_row_membership n m lit1_l lit2_l u v); exact Hw.
Qed.

Lemma twosat_prefix_reverse_edge_full :
  forall n m lit1_l lit2_l u v,
    twosat_clause_input_wf n m lit1_l lit2_l ->
    twosat_prefix_reverse_edge m lit1_l lit2_l u v <->
      In v (twosat_reverse_row m lit1_l lit2_l u).
Proof.
  intros n m lit1_l lit2_l u v Hw.
  unfold twosat_prefix_reverse_edge. symmetry.
  apply (twosat_reverse_row_membership n m lit1_l lit2_l u v); exact Hw.
Qed.

Lemma twosat_csr2_faithful_canonical :
  forall n m lit1_l lit2_l fadj_col_l fadj_row_l
         radj_col_l radj_row_l fcur_l rcur_l,
    twosat_clause_input_wf n m lit1_l lit2_l ->
    twosat_processed_complete n m lit1_l lit2_l
      fadj_col_l fadj_row_l radj_col_l radj_row_l fcur_l rcur_l ->
    csr2_faithful (twosat_canonical_graph n m lit1_l lit2_l)
      fadj_col_l fadj_row_l.
Proof.
  intros n m lit1_l lit2_l fadj_col_l fadj_row_l
    radj_col_l radj_row_l fcur_l rcur_l Hw Hcomplete.
  unfold csr2_faithful.
  intros u v Hu Hv.
  change (0 <= u < 2 * n)%Z in Hu.
  change (0 <= v < 2 * n)%Z in Hv.
  destruct Hcomplete as [Hpp [Hbounds [Hrows [Hcur [Hfwd Hrev]]]]].
  pose proof (Hfwd u v Hu Hv) as Hfwd_uv.
  rewrite (proj1 (Hcur u Hu)) in Hfwd_uv.
  transitivity (In v (twosat_forward_row m lit1_l lit2_l u)).
  - apply (twosat_step_canonical_forward
      n m lit1_l lit2_l u v Hw Hu Hv).
  - split.
    + intro Hrow.
      pose proof (proj2 (twosat_prefix_edge_full
        n m lit1_l lit2_l u v Hw) Hrow) as Hpre.
      destruct (proj1 Hfwd_uv Hpre) as [j [Hlo [Hhi Heq]]].
      exists j. split; [split; assumption|assumption].
    + intro Hex.
      destruct Hex as [j [[Hlo Hhi] Heq]].
      apply (proj1 (twosat_prefix_edge_full
        n m lit1_l lit2_l u v Hw)).
      apply (proj2 Hfwd_uv).
      exists j. exact (conj Hlo (conj Hhi Heq)).
Qed.

Lemma twosat_csr1_faithful_canonical :
  forall n m lit1_l lit2_l fadj_col_l fadj_row_l
         radj_col_l radj_row_l fcur_l rcur_l,
    twosat_clause_input_wf n m lit1_l lit2_l ->
    twosat_processed_complete n m lit1_l lit2_l
      fadj_col_l fadj_row_l radj_col_l radj_row_l fcur_l rcur_l ->
    csr1_faithful (twosat_canonical_graph n m lit1_l lit2_l)
      radj_col_l radj_row_l.
Proof.
  intros n m lit1_l lit2_l fadj_col_l fadj_row_l
    radj_col_l radj_row_l fcur_l rcur_l Hw Hcomplete.
  unfold csr1_faithful.
  intros u v Hu Hv.
  change (0 <= u < 2 * n)%Z in Hu.
  change (0 <= v < 2 * n)%Z in Hv.
  destruct Hcomplete as [Hpp [Hbounds [Hrows [Hcur [Hfwd Hrev]]]]].
  pose proof (Hrev u v Hu Hv) as Hrev_uv.
  rewrite (proj2 (Hcur u Hu)) in Hrev_uv.
  transitivity (In v (twosat_reverse_row m lit1_l lit2_l u)).
  - transitivity (In u (twosat_forward_row m lit1_l lit2_l v)).
    + apply (twosat_step_canonical_forward
        n m lit1_l lit2_l v u Hw Hv Hu).
    + apply (twosat_forward_row_reverse m lit1_l lit2_l v u).
  - split.
    + intro Hrow.
      pose proof (proj2 (twosat_prefix_reverse_edge_full
        n m lit1_l lit2_l u v Hw) Hrow) as Hpre.
      destruct (proj1 Hrev_uv Hpre) as [j [Hlo [Hhi Heq]]].
      exists j. split; [split; assumption|assumption].
    + intro Hex.
      destruct Hex as [j [[Hlo Hhi] Heq]].
      apply (proj1 (twosat_prefix_reverse_edge_full
        n m lit1_l lit2_l u v Hw)).
      apply (proj2 Hrev_uv).
      exists j. exact (conj Hlo (conj Hhi Heq)).
Qed.

Lemma twosat_kosaraju_graph_canonical :
  forall n m lit1_l lit2_l fadj_col_l fadj_row_l
         radj_col_l radj_row_l fcur_l rcur_l,
    twosat_clause_input_wf n m lit1_l lit2_l ->
    twosat_csr_wf n fadj_col_l fadj_row_l radj_col_l radj_row_l ->
    twosat_processed_complete n m lit1_l lit2_l
      fadj_col_l fadj_row_l radj_col_l radj_row_l fcur_l rcur_l ->
    twosat_kosaraju_graph n m lit1_l lit2_l
      fadj_col_l fadj_row_l radj_col_l radj_row_l.
Proof.
  intros n m lit1_l lit2_l fadj_col_l fadj_row_l
    radj_col_l radj_row_l fcur_l rcur_l Hinput Hcsr Hcomplete.
  destruct Hinput as [Hn [Hm [Hlit1 [Hlit2 Hbounds]]]].
  assert (Hinput' : twosat_clause_input_wf n m lit1_l lit2_l).
  { exact (conj Hn (conj Hm (conj Hlit1 (conj Hlit2 Hbounds)))). }
  unfold twosat_kosaraju_graph.
  split; [exact Hcsr|].
  split; [exact Hlit1|].
  split; [exact Hlit2|].
  exists (twosat_canonical_graph n m lit1_l lit2_l).
  split; [reflexivity|].
  assert (Hvalid : twosat_adj_graph_valid
    (twosat_canonical_graph n m lit1_l lit2_l)).
  { apply twosat_canonical_graph_valid; exact Hinput'. }
  assert (Hedges : twosat_graph_edges n m lit1_l lit2_l
    (twosat_canonical_graph n m lit1_l lit2_l)).
  { apply twosat_graph_edges_canonical; exact Hinput'. }
  assert (Hfwd : csr2_faithful
    (twosat_canonical_graph n m lit1_l lit2_l) fadj_col_l fadj_row_l).
  { apply (twosat_csr2_faithful_canonical n m lit1_l lit2_l
      fadj_col_l fadj_row_l radj_col_l radj_row_l fcur_l rcur_l);
    [exact Hinput'|exact Hcomplete]. }
  assert (Hrev : csr1_faithful
    (twosat_canonical_graph n m lit1_l lit2_l) radj_col_l radj_row_l).
  { apply (twosat_csr1_faithful_canonical n m lit1_l lit2_l
      fadj_col_l fadj_row_l radj_col_l radj_row_l fcur_l rcur_l);
    [exact Hinput'|exact Hcomplete]. }
  split; [exact Hvalid|].
  split; [exact Hedges|].
  split; [exact Hfwd|exact Hrev].
Qed.

(* Partial CSR bridge for the clause-construction loop.  The row arrays
   are fixed by the counting/prefix passes; only the cursor-occupied
   portions of the packed columns are constrained before loop exit. *)
Definition twosat_csr_row_shape
  (n m : Z) (fadj_row_l radj_row_l : list Z) : Prop :=
  Zlength fadj_row_l = 2 * n + 1 /\
  Zlength radj_row_l = 2 * n + 1 /\
  m_of fadj_row_l = 2 * m /\
  m_of radj_row_l = 2 * m /\
  (forall u, 0 <= u < 2 * n ->
     0 <= csr_lo u fadj_row_l /\
     csr_hi u fadj_row_l <= 2 * m /\
     csr_lo u fadj_row_l <= csr_hi u fadj_row_l) /\
  (forall u, 0 <= u < 2 * n ->
     0 <= csr_lo u radj_row_l /\
     csr_hi u radj_row_l <= 2 * m /\
     csr_lo u radj_row_l <= csr_hi u radj_row_l) /\
  (forall u, 0 <= u < 2 * n - 1 ->
     csr_hi u fadj_row_l <= csr_hi (u + 1) fadj_row_l) /\
  (forall u, 0 <= u < 2 * n - 1 ->
     csr_hi u radj_row_l <= csr_hi (u + 1) radj_row_l).

Definition twosat_csr_array_shape
  (n m : Z) (fadj_col_l fadj_row_l radj_col_l radj_row_l : list Z) : Prop :=
  Zlength fadj_col_l = 2 * m /\
  Zlength radj_col_l = 2 * m /\
  twosat_csr_row_shape n m fadj_row_l radj_row_l.

Definition twosat_csr_row_cover
  (n m : Z) (fadj_row_l radj_row_l : list Z) : Prop :=
  (forall j, 0 <= j < 2 * m ->
     exists u, 0 <= u < 2 * n /\
       csr_lo u fadj_row_l <= j /\ j < csr_hi u fadj_row_l) /\
  (forall j, 0 <= j < 2 * m ->
     exists u, 0 <= u < 2 * n /\
       csr_lo u radj_row_l <= j /\ j < csr_hi u radj_row_l).

Definition twosat_csr_written_range
  (n : Z) (fadj_col_l fadj_row_l fcur_l
         radj_col_l radj_row_l rcur_l : list Z) : Prop :=
  (forall u, 0 <= u < 2 * n ->
     forall j, csr_lo u fadj_row_l <= j ->
       j < Znth u fcur_l 0 ->
       0 <= Znth j fadj_col_l 0 < 2 * n) /\
  (forall u, 0 <= u < 2 * n ->
     forall j, csr_lo u radj_row_l <= j ->
       j < Znth u rcur_l 0 ->
       0 <= Znth j radj_col_l 0 < 2 * n).

Definition twosat_partial_csr_bridge
  (n m i : Z) (fadj_col_l fadj_row_l fcur_l
               radj_col_l radj_row_l rcur_l : list Z) : Prop :=
  twosat_csr_array_shape n m fadj_col_l fadj_row_l radj_col_l radj_row_l /\
  twosat_csr_row_cover n m fadj_row_l radj_row_l /\
  twosat_csr_written_range n fadj_col_l fadj_row_l fcur_l
    radj_col_l radj_row_l rcur_l.

Lemma twosat_partial_csr_bridge_complete :
  forall n m fadj_col_l fadj_row_l radj_col_l radj_row_l fcur_l rcur_l,
    twosat_partial_csr_bridge n m m
      fadj_col_l fadj_row_l fcur_l radj_col_l radj_row_l rcur_l ->
    (forall u, 0 <= u < 2 * n ->
      Znth u fcur_l 0 = csr_hi u fadj_row_l /\
      Znth u rcur_l 0 = csr_hi u radj_row_l) ->
    twosat_csr_wf n fadj_col_l fadj_row_l radj_col_l radj_row_l.
Proof.
  intros n m fadj_col_l fadj_row_l radj_col_l radj_row_l fcur_l rcur_l
    Hbridge Hcur.
  destruct Hbridge as [Hshape [Hcover Hwritten]].
  unfold twosat_csr_wf.
  destruct Hshape as [Hfcol [Hrcol [Hfrow [Hrrow [Hmf [Hmr
    [Hfbound [Hrbound [Hfmono Hrmono]]]]]]]]].
  destruct Hcover as [Hfcover Hrcov].
  destruct Hwritten as [Hfwritten Hrwrit].
  split; [exact Hfrow|].
  split; [exact Hrrow|].
  split; [rewrite Hmf, Hfcol; reflexivity|].
  split; [rewrite Hmr, Hrcol; reflexivity|].
  split; [rewrite Hmf, Hmr; reflexivity|].
  split; [intros u Hu; exact (proj1 (Hfbound u Hu))|].
  split; [intros u Hu; rewrite Hmf;
    exact (proj1 (proj2 (Hfbound u Hu)))|].
  split; [intros u Hu; exact (proj1 (Hrbound u Hu))|].
  split; [intros u Hu; rewrite Hmr;
    exact (proj1 (proj2 (Hrbound u Hu)))|].
  split; [intros j Hj|].
    rewrite Hmf in Hj.
    destruct (Hfcover j Hj) as [u [Hu [Hlo Hhi]]].
    rewrite <- (proj1 (Hcur u Hu)) in Hhi.
    exact (Hfwritten u Hu j Hlo Hhi).
  split; [intros j Hj|].
    rewrite Hmr in Hj.
    destruct (Hrcov j Hj) as [u [Hu [Hlo Hhi]]].
    rewrite <- (proj2 (Hcur u Hu)) in Hhi.
    exact (Hrwrit u Hu j Hlo Hhi).
  split; [intros u Hu; exact (proj2 (proj2 (Hfbound u Hu)))|].
  split; [intros u Hu; exact (proj2 (proj2 (Hrbound u Hu)))|].
  split; [intros u Hu; exact (Hfmono u Hu)|
    intros u Hu; exact (Hrmono u Hu)].
Qed.

(* Conflict detection via SCC IDs                                    *)
(*                                                                   *)
(* After Kosaraju, sid[u] is the SCC identifier of vertex u.
   If sid[2*(v-1)] = sid[2*(v-1)+1], the two literals of variable v
   are in the same SCC, which implies unsatisfiability.            *)
(* ================================================================ *)

Definition no_conflict_by_sid (sid_l : list Z) (n : Z) : Prop :=
  forall v, 1 <= v <= n ->
    Znth (2*(v-1)) sid_l 0 <> Znth (2*(v-1)+1) sid_l 0.

(* ================================================================ *)
(* High-level KosarajuGraph assertion                               *)
(*                                                                  *)
(* After building the 2SAT implication graph in CSR format          *)
(* (fadj_row/col, radj_row/col), this predicate asserts that the    *)
(* data structures encode a KosarajuGraph with 2*n vertices.        *)
(*                                                                  *)
(* The AdjGraph existential witnesses that the CSR arrays define    *)
(* an abstract graph satisfying AdjGraphValid (→ all typeclass      *)
(* requirements of KosarajuGraph) and the csr*_faithful predicates  *)
(* tie the concrete CSR encoding to the abstract step relation.     *)
(* ================================================================ *)
