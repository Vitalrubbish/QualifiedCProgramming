Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import Lia.
Require Import Algorithms.TwoSAT.TwoSAT.
From AUXLib Require Import int_auto.
From SimpleC.SL Require Import Mem SeparationLogic.
From GraphLib Require Import reachable_basic.
Require Import RelsDomain.
From MonadLib.MonadErr Require Import monadesafe_lib.
Import ListNotations.
Local Open Scope Z_scope.

From SimpleC.EE.QCP_demos_LLM Require Import kosaraju_rel_lib.

Definition csr_layout
  (g : AdjGraph) (col_l row_l : list Z) : Prop :=
  Zlength row_l = adj_verts g + 1 /\
  m_of row_l = Zlength col_l /\
  csr_lo 0 row_l = 0 /\
  (forall u, 0 <= u < adj_verts g ->
     0 <= csr_lo u row_l /\
     csr_lo u row_l <= csr_hi u row_l /\
     csr_hi u row_l <= m_of row_l) /\
  (forall u, 0 <= u < adj_verts g - 1 ->
     csr_hi u row_l <= csr_hi (u + 1) row_l) /\
  (forall j, 0 <= j < m_of row_l ->
     0 <= Znth j col_l 0 < adj_verts g).

Definition transpose_spec
  (g : AdjGraph) (fadj_col_l fadj_row_l radj_col_l radj_row_l : list Z)
  (n : Z) : Prop :=
  adj_verts g = n /\
  AdjGraphValid g /\
  m_of fadj_row_l = m_of radj_row_l /\
  csr2_faithful g fadj_col_l fadj_row_l /\
  csr_layout g radj_col_l radj_row_l /\
  csr1_faithful g radj_col_l radj_row_l.

Definition fin_values_in_int_range (fin_l : list Z) (n : Z) : Prop :=
  forall v, 0 <= v < n -> 0 <= Znth v fin_l 0 <= INT_MAX.

Definition order_spec (fin_l order_l : list Z) (n : Z) : Prop :=
  Zlength fin_l = n /\
  fin_values_in_int_range fin_l n /\
  Permutation order_l (map Z.of_nat (seq 0 (Z.to_nat n))) /\
  (forall i j, 0 <= i /\ i < j /\ j < n ->
     Znth (Znth i order_l 0) fin_l 0 >=
     Znth (Znth j order_l 0) fin_l 0).

Definition mutually_reachable (g : AdjGraph) (u v : Z) : Prop :=
  reachable g u v /\ reachable g v u.

Definition dfs1_timer_surplus_preserved
  (vis1_l vis1_l_ : list Z) (timer_v timer_v_ : Z) : Prop :=
  forall spare,
    0 <= spare ->
    timer_v + spare <= count_nonzero vis1_l ->
    timer_v_ + spare <= count_nonzero vis1_l_.

Definition dfs1_active_timer_surplus
  (vis1_l vis1_m : list Z) (timer_v timer_m : Z) : Prop :=
  forall spare,
    0 <= spare ->
    timer_v + spare <= count_nonzero vis1_l ->
    timer_m + spare + 1 <= count_nonzero vis1_m.

Definition dfs1_high_level_post
  (g : AdjGraph) (radj_col_l radj_row_l vis1_l fin_l vis1_l_ fin_l_ : list Z)
  (u timer_v timer_v_ n : Z) : Prop :=
  adj_verts g = n /\
  csr_wf1 g radj_col_l radj_row_l vis1_l_ fin_l_ /\
  csr1_faithful g radj_col_l radj_row_l /\
  0 <= u < n /\
  0 <= timer_v <= timer_v_ /\
  timer_v <= count_nonzero vis1_l /\
  timer_v_ <= count_nonzero vis1_l_ /\
  dfs1_timer_surplus_preserved vis1_l vis1_l_ timer_v timer_v_ /\
  fin_values_in_int_range fin_l n /\
  fin_values_in_int_range fin_l_ n /\
  Znth u vis1_l_ 0 <> 0 /\
  (forall w, 0 <= w < n ->
     Znth w vis1_l 0 <> 0 -> Znth w vis1_l_ 0 <> 0).

Definition dfs2_high_level_post
  (g : AdjGraph) (fadj_col_l fadj_row_l vis2_l sid_l vis2_l_ sid_l_ : list Z)
  (root u n : Z) : Prop :=
  adj_verts g = n /\
  csr_wf2 g fadj_col_l fadj_row_l vis2_l_ sid_l_ /\
  csr2_faithful g fadj_col_l fadj_row_l /\
  0 <= root < n /\
  0 <= u < n /\
  Znth u vis2_l_ 0 <> 0 /\
  (forall w, 0 <= w < n ->
     Znth w vis2_l 0 <> 0 -> Znth w vis2_l_ 0 <> 0).

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

(* Guarded graph validity for this Z-indexed case.  It matches the shared
   valid-vertex graph predicate: Z.to_nat must not expose negative indices
   as vertex zero. *)
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
Require Import ListLib.General.Length.
Import ListNotations.

Lemma twosat_firstn_succ_nth_r13 :
  forall (A : Type) (k : nat) (l : list A) (d : A),
    (k < length l)%nat -> firstn (S k) l = firstn k l ++ (nth k l d :: nil).
Proof.
  intros A k. induction k as [|k IH]; intros l d H.
  - destruct l as [|x xs]; [inversion H|reflexivity].
  - destruct l as [|x xs]; [inversion H|].
    change (x :: firstn (S k) xs = x :: (firstn k xs ++ (nth k xs d :: nil))).
    f_equal. apply IH. apply (proj2 (Nat.succ_lt_mono k (length xs))). exact H.
Qed.

Lemma twosat_filter_length_snoc_r13 :
  forall (A : Type) (f : A -> bool) (l : list A) (x : A),
    Zlength (filter f (l ++ (x :: nil))) = Zlength (filter f l) + (if f x then 1 else 0).
Proof.
  intros. rewrite filter_app, Zlength_app. simpl.
  destruct (f x); simpl; rewrite ?Zlength_cons, ?Zlength_nil; simpl; lia.
Qed.

Lemma twosat_firstn_Zsucc_nth_r13 :
  forall (A : Type) (i : Z) (l : list A) (d : A),
    0 <= i -> i < Zlength l ->
    firstn (Z.to_nat (i + 1)) l = firstn (Z.to_nat i) l ++ (Znth i l d :: nil).
Proof.
  intros A i l d Hi Hil. replace (i + 1) with (Z.succ i) by lia.
  rewrite Z2Nat.inj_succ by lia. apply twosat_firstn_succ_nth_r13.
  assert (H : (Z.to_nat i < Z.to_nat (Z.of_nat (length l)))%nat).
  { apply (proj1 (Z2Nat.inj_lt i (Z.of_nat (length l)) ltac:(lia) ltac:(lia))).
    rewrite Zlength_correct in Hil. exact Hil. }
  replace (Z.to_nat (Z.of_nat (length l))) with (length l) in H by lia. exact H.
Qed.

Lemma twosat_fdegree_succ_r13 :
  forall i lit1_l lit2_l u, 0 <= i -> i < Zlength lit1_l -> i < Zlength lit2_l ->
    twosat_fdegree (i + 1) lit1_l lit2_l u = twosat_fdegree i lit1_l lit2_l u +
      (if Z.eqb (neg_vertex (Znth i lit1_l 0)) u then 1 else 0) +
      (if Z.eqb (neg_vertex (Znth i lit2_l 0)) u then 1 else 0).
Proof.
  intros i lit1_l lit2_l u Hi H1 H2. unfold twosat_fdegree.
  rewrite (twosat_firstn_Zsucc_nth_r13 Z i lit1_l 0 Hi H1).
  rewrite (twosat_firstn_Zsucc_nth_r13 Z i lit2_l 0 Hi H2).
  repeat rewrite twosat_filter_length_snoc_r13. lia.
Qed.

Lemma twosat_rdegree_succ_r13 :
  forall i lit1_l lit2_l u, 0 <= i -> i < Zlength lit1_l -> i < Zlength lit2_l ->
    twosat_rdegree (i + 1) lit1_l lit2_l u = twosat_rdegree i lit1_l lit2_l u +
      (if Z.eqb (lit_to_vertex (Znth i lit2_l 0)) u then 1 else 0) +
      (if Z.eqb (lit_to_vertex (Znth i lit1_l 0)) u then 1 else 0).
Proof.
  intros i lit1_l lit2_l u Hi H1 H2. unfold twosat_rdegree.
  rewrite (twosat_firstn_Zsucc_nth_r13 Z i lit2_l 0 Hi H2).
  rewrite (twosat_firstn_Zsucc_nth_r13 Z i lit1_l 0 Hi H1).
  repeat rewrite twosat_filter_length_snoc_r13. lia.
Qed.

Lemma twosat_filter_firstn_length_mono_r13 :
  forall (A : Type) (f : A -> bool) (i j : nat) (l : list A), (i <= j)%nat ->
    Zlength (filter f (firstn i l)) <= Zlength (filter f (firstn j l)).
Proof.
  intros A f i j l Hij. pose proof (firstn_skipn i (firstn j l)) as Hsplit.
  rewrite firstn_firstn, (min_l i j Hij) in Hsplit.
  pose proof (f_equal (fun xs : list A => Zlength xs) (f_equal (filter f) Hsplit)) as Hlen.
  rewrite filter_app, Zlength_app in Hlen.
  pose proof (Zlength_nonneg (filter f (skipn i (firstn j l)))) as Hnonneg. lia.
Qed.

Lemma twosat_fdegree_mono_r13 :
  forall i j lit1_l lit2_l u, 0 <= i -> i <= j -> j <= Zlength lit1_l -> j <= Zlength lit2_l ->
    twosat_fdegree i lit1_l lit2_l u <= twosat_fdegree j lit1_l lit2_l u.
Proof.
  intros i j lit1_l lit2_l u Hi Hij Hj1 Hj2.
  assert (Hj : 0 <= j) by (pose proof (Zlength_nonneg lit1_l); lia).
  assert (Hin : (Z.to_nat i <= Z.to_nat j)%nat).
  { apply (proj1 (Z2Nat.inj_le i j Hi Hj)); exact Hij. }
  unfold twosat_fdegree.
  pose proof (twosat_filter_firstn_length_mono_r13 Z (fun a => Z.eqb (neg_vertex a) u)
    (Z.to_nat i) (Z.to_nat j) lit1_l Hin) as H1.
  pose proof (twosat_filter_firstn_length_mono_r13 Z (fun b => Z.eqb (neg_vertex b) u)
    (Z.to_nat i) (Z.to_nat j) lit2_l Hin) as H2. lia.
Qed.

Lemma twosat_rdegree_mono_r13 :
  forall i j lit1_l lit2_l u, 0 <= i -> i <= j -> j <= Zlength lit1_l -> j <= Zlength lit2_l ->
    twosat_rdegree i lit1_l lit2_l u <= twosat_rdegree j lit1_l lit2_l u.
Proof.
  intros i j lit1_l lit2_l u Hi Hij Hj1 Hj2.
  assert (Hj : 0 <= j) by (pose proof (Zlength_nonneg lit1_l); lia).
  assert (Hin : (Z.to_nat i <= Z.to_nat j)%nat).
  { apply (proj1 (Z2Nat.inj_le i j Hi Hj)); exact Hij. }
  unfold twosat_rdegree.
  pose proof (twosat_filter_firstn_length_mono_r13 Z (fun b => Z.eqb (lit_to_vertex b) u)
    (Z.to_nat i) (Z.to_nat j) lit2_l Hin) as H1.
  pose proof (twosat_filter_firstn_length_mono_r13 Z (fun a => Z.eqb (lit_to_vertex a) u)
    (Z.to_nat i) (Z.to_nat j) lit1_l Hin) as H2. lia.
Qed.

Lemma twosat_forward_slots_strict_r13 :
  forall n m i lit1_l lit2_l fadj_l fcur_l a b na nb va vb p r,
    0 <= i -> i < m -> Zlength lit1_l = m -> Zlength lit2_l = m ->
    0 <= na < 2 * n -> 0 <= nb < 2 * n ->
    a = Znth i lit1_l 0 -> b = Znth i lit2_l 0 ->
    twosat_clause_encoding a b na nb va vb ->
    (forall u, 0 <= u < 2 * n -> csr_hi u fadj_l = csr_lo u fadj_l + twosat_fdegree m lit1_l lit2_l u) ->
    (forall u, 0 <= u < 2 * n -> Znth u fcur_l 0 = csr_lo u fadj_l + twosat_fdegree i lit1_l lit2_l u) ->
    p = Znth na fcur_l 0 -> (na = nb -> r = Znth nb fcur_l 0 + 1) ->
    (na <> nb -> r = Znth nb fcur_l 0) -> csr_lo na fadj_l <= p -> csr_lo nb fadj_l <= r ->
    csr_lo na fadj_l <= p < csr_hi na fadj_l /\ csr_lo nb fadj_l <= r < csr_hi nb fadj_l.
Proof.
  intros n m i l1 l2 row cur a b na nb va vb p r Hi Him Hl1 Hl2 Hna Hnb Ha Hb Henc Hrows Hocc Hp Hsame Hdiff Hplo Hrlo.
  destruct Henc as [Ena [Enb [Eva Evb]]].
  assert (Ea : Z.eqb (neg_vertex (Znth i l1 0)) na = true).
  { apply Z.eqb_eq. rewrite <- Ha, Ena. reflexivity. }
  assert (Eb : Z.eqb (neg_vertex (Znth i l2 0)) nb = true).
  { apply Z.eqb_eq. rewrite <- Hb, Enb. reflexivity. }
  pose proof (twosat_fdegree_succ_r13 i l1 l2 na Hi ltac:(lia) ltac:(lia)) as Sna.
  pose proof (twosat_fdegree_succ_r13 i l1 l2 nb Hi ltac:(lia) ltac:(lia)) as Snb.
  rewrite Ea in Sna. rewrite Eb in Snb.
  pose proof (twosat_fdegree_mono_r13 (i+1) m l1 l2 na ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as Mna.
  pose proof (twosat_fdegree_mono_r13 (i+1) m l1 l2 nb ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as Mnb.
  assert (Dna : twosat_fdegree i l1 l2 na + 1 <= twosat_fdegree m l1 l2 na).
  { destruct (Z.eqb (neg_vertex (Znth i l2 0)) na); simpl in Sna; lia. }
  assert (Dnb : twosat_fdegree i l1 l2 nb + 1 <= twosat_fdegree m l1 l2 nb).
  { destruct (Z.eqb (neg_vertex (Znth i l1 0)) nb); simpl in Snb; lia. }
  split.
  - split; [exact Hplo|].
    pose proof (Hocc na Hna) as Opa. pose proof (Hrows na Hna) as Rpa.
    assert (Pna : p = csr_lo na row + twosat_fdegree i l1 l2 na).
    { rewrite Hp. exact Opa. }
    replace (csr_hi na row) with (csr_lo na row + twosat_fdegree m l1 l2 na) by (symmetry; exact Rpa).
    lia.
  - split; [exact Hrlo|]. destruct (Z.eq_dec na nb) as [Heq|Heq].
    + pose proof (Hocc nb Hnb) as Opb. pose proof (Hrows nb Hnb) as Rpb.
      assert (Rnb : r = csr_lo nb row + twosat_fdegree i l1 l2 nb + 1).
      { rewrite (Hsame Heq), Opb. lia. }
      assert (Dnb2 : twosat_fdegree i l1 l2 nb + 2 <= twosat_fdegree m l1 l2 nb).
      { assert (E : Z.eqb (neg_vertex (Znth i l1 0)) nb = true).
        { apply Z.eqb_eq. rewrite <- Ha, <- Heq, Ena. reflexivity. }
        rewrite E in Snb. lia. }
      replace (csr_hi nb row) with (csr_lo nb row + twosat_fdegree m l1 l2 nb) by (symmetry; exact Rpb).
      pose proof Dnb2. lia.
    + pose proof (Hocc nb Hnb) as Opb. pose proof (Hrows nb Hnb) as Rpb.
      assert (Rnb : r = csr_lo nb row + twosat_fdegree i l1 l2 nb).
      { rewrite (Hdiff Heq), Opb. exact eq_refl. }
      replace (csr_hi nb row) with (csr_lo nb row + twosat_fdegree m l1 l2 nb) by (symmetry; exact Rpb).
      lia.
Qed.

Lemma twosat_reverse_slots_strict_r13 :
  forall n m i lit1_l lit2_l radj_l rcur_l a b na nb va vb q s,
    0 <= i -> i < m -> Zlength lit1_l = m -> Zlength lit2_l = m ->
    0 <= va < 2 * n -> 0 <= vb < 2 * n ->
    a = Znth i lit1_l 0 -> b = Znth i lit2_l 0 -> twosat_clause_encoding a b na nb va vb ->
    (forall u, 0 <= u < 2 * n -> csr_hi u radj_l = csr_lo u radj_l + twosat_rdegree m lit1_l lit2_l u) ->
    (forall u, 0 <= u < 2 * n -> Znth u rcur_l 0 = csr_lo u radj_l + twosat_rdegree i lit1_l lit2_l u) ->
    q = Znth vb rcur_l 0 -> (vb = va -> s = Znth va rcur_l 0 + 1) ->
    (vb <> va -> s = Znth va rcur_l 0) -> csr_lo vb radj_l <= q -> csr_lo va radj_l <= s ->
    csr_lo vb radj_l <= q < csr_hi vb radj_l /\ csr_lo va radj_l <= s < csr_hi va radj_l.
Proof.
  intros n m i l1 l2 row cur a b na nb va vb q s Hi Him Hl1 Hl2 Hva Hvb Ha Hb Henc Hrows Hocc Hq Hsame Hdiff Hqlo Hslo.
  destruct Henc as [Ena [Enb [Eva Evb]]].
  assert (Ea : Z.eqb (lit_to_vertex (Znth i l1 0)) va = true).
  { apply Z.eqb_eq. rewrite <- Ha, Eva. reflexivity. }
  assert (Eb : Z.eqb (lit_to_vertex (Znth i l2 0)) vb = true).
  { apply Z.eqb_eq. rewrite <- Hb, Evb. reflexivity. }
  pose proof (twosat_rdegree_succ_r13 i l1 l2 va Hi ltac:(lia) ltac:(lia)) as SvaSucc.
  pose proof (twosat_rdegree_succ_r13 i l1 l2 vb Hi ltac:(lia) ltac:(lia)) as SvbSucc.
  rewrite Ea in SvaSucc. rewrite Eb in SvbSucc.
  pose proof (twosat_rdegree_mono_r13 (i+1) m l1 l2 va ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as Mva.
  pose proof (twosat_rdegree_mono_r13 (i+1) m l1 l2 vb ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as Mvb.
  assert (Dva : twosat_rdegree i l1 l2 va + 1 <= twosat_rdegree m l1 l2 va).
  { destruct (Z.eqb (lit_to_vertex (Znth i l2 0)) va); simpl in SvaSucc; lia. }
  assert (Dvb : twosat_rdegree i l1 l2 vb + 1 <= twosat_rdegree m l1 l2 vb).
  { destruct (Z.eqb (lit_to_vertex (Znth i l1 0)) vb); simpl in SvbSucc; lia. }
  split.
  - split; [exact Hqlo|].
    pose proof (Hocc vb Hvb) as Orvb. pose proof (Hrows vb Hvb) as Rrvb.
    assert (Qvb : q = csr_lo vb row + twosat_rdegree i l1 l2 vb).
    { rewrite Hq. exact Orvb. }
    replace (csr_hi vb row) with (csr_lo vb row + twosat_rdegree m l1 l2 vb) by (symmetry; exact Rrvb).
    lia.
  - split; [exact Hslo|]. destruct (Z.eq_dec vb va) as [Heq|Heq].
    + pose proof (Hocc va Hva) as Orva. pose proof (Hrows va Hva) as Rrva.
      assert (Sva : s = csr_lo va row + twosat_rdegree i l1 l2 va + 1).
      { rewrite (Hsame Heq), Orva. lia. }
      assert (Dva2 : twosat_rdegree i l1 l2 va + 2 <= twosat_rdegree m l1 l2 va).
      { assert (E : Z.eqb (lit_to_vertex (Znth i l2 0)) va = true).
        { apply Z.eqb_eq. rewrite <- Hb, <- Heq, Evb. reflexivity. }
        rewrite E in SvaSucc. lia. }
      replace (csr_hi va row) with (csr_lo va row + twosat_rdegree m l1 l2 va) by (symmetry; exact Rrva).
      pose proof Dva2. lia.
    + pose proof (Hocc va Hva) as Orva. pose proof (Hrows va Hva) as Rrva.
      assert (Sva : s = csr_lo va row + twosat_rdegree i l1 l2 va).
      { rewrite (Hdiff Heq), Orva. exact eq_refl. }
      replace (csr_hi va row) with (csr_lo va row + twosat_rdegree m l1 l2 va) by (symmetry; exact Rrva).
      lia.
Qed.

Lemma twosat_old_cell_distinct_from_two_writes_r13 :
  forall n row_l cur_l u j row_q row_s q s,
    0 <= u < 2 * n -> 0 <= row_q < 2 * n -> 0 <= row_s < 2 * n ->
    (forall x, 0 <= x < 2 * n -> csr_lo x row_l <= Znth x cur_l 0 /\ Znth x cur_l 0 <= csr_hi x row_l) ->
    (forall x y, 0 <= x < 2 * n -> 0 <= y < 2 * n -> x < y -> csr_hi x row_l <= csr_lo y row_l) ->
    q = Znth row_q cur_l 0 -> Znth row_s cur_l 0 <= s ->
    csr_lo row_q row_l <= q -> q < csr_hi row_q row_l -> csr_lo row_s row_l <= s -> s < csr_hi row_s row_l ->
    csr_lo u row_l <= j -> j < Znth u cur_l 0 -> j <> q /\ j <> s.
Proof.
  intros n row cur u j rq rs q s Hu Hrq Hrs Hb Hcut Hqcur Hscur Hqlo Hqhi Hslo Hshi Hjlo Hjcur.
  assert (Hjhi : j < csr_hi u row).
  { pose proof (proj2 (Hb u Hu)) as H. lia. }
  split.
  - destruct (Z.eq_dec u rq) as [E|E].
    + subst u. intro X. subst j. rewrite Hqcur in Hjcur. lia.
    + destruct (Z.lt_trichotomy u rq) as [L|L].
      * pose proof (Hcut u rq Hu Hrq L) as C. intro X. subst j. lia.
      * destruct L as [Eeq|G].
        { exfalso; apply E; exact Eeq. }
        pose proof (Hcut rq u Hrq Hu G) as C. intro X. subst j. lia.
  - destruct (Z.eq_dec u rs) as [E|E].
    + subst u. intro X. subst j. lia.
    + destruct (Z.lt_trichotomy u rs) as [L|L].
      * pose proof (Hcut u rs Hu Hrs L) as C. intro X. subst j. lia.
      * destruct L as [Eeq|G].
        { exfalso; apply E; exact Eeq. }
        pose proof (Hcut rs u Hrs Hu G) as C. intro X. subst j. lia.
Qed.



Lemma twosat_replace_two_existential_transport_bounded_r18 :
  forall (n : Z) (col : list Z) (lo oldcur newcur q s na nb u va vb : Z)
         (P : Z -> Prop),
    0 <= lo ->
    0 <= q < Zlength col -> 0 <= s < Zlength col -> q <> s ->
    lo <= q -> lo <= s -> q < newcur -> s < newcur ->
    oldcur <= Zlength col -> newcur <= Zlength col ->
    (forall j, lo <= j -> j < oldcur -> j <> q /\ j <> s) ->
    (forall j, lo <= j -> j < oldcur -> j < newcur) ->
    (forall j, lo <= j -> j < newcur ->
      j = q \/ j = s \/ j < oldcur) ->
    (forall j, lo <= j -> j < newcur -> j = q -> u = vb) ->
    (forall j, lo <= j -> j < newcur -> j = s -> u = va) ->
    (forall w, 0 <= w < 2 * n ->
      (P w <->
        exists j, lo <= j /\ j < oldcur /\ Znth j col 0 = w)) ->
    forall v, 0 <= v < 2 * n ->
      (P v \/ (u = vb /\ v = na) \/ (u = va /\ v = nb)) <->
      exists j, lo <= j /\ j < newcur /\
        Znth j (replace_Znth s nb (replace_Znth q na col)) 0 = v.
Proof.
  intros n col lo oldcur newcur q s na nb u va vb P Hlo Hq Hs Hqs Hqlo Hslo
    Hqnew Hsnew Holdlen Hnewlen Hdistinct Hkeep Hdecomp Hqsrc Hssrc Hfaith
    v Hv.
  assert (Hq' : 0 <= q < Zlength (replace_Znth s nb (replace_Znth q na col))).
  { rewrite Zlength_replace_Znth. rewrite Zlength_replace_Znth. exact Hq. }
  assert (Hq_inner : 0 <= q < Zlength (replace_Znth q na col)).
  { rewrite Zlength_replace_Znth. exact Hq. }
  assert (Hs' : 0 <= s < Zlength (replace_Znth q na col)).
  { rewrite Zlength_replace_Znth. exact Hs. }
  assert (Hqv : Znth q (replace_Znth s nb (replace_Znth q na col)) 0 = na).
  { rewrite Znth_replace_Znth_Diff.
    - apply Znth_replace_Znth_Same. exact Hq.
    - exact Hs'.
    - exact Hq_inner.
    - intro E. apply Hqs. symmetry. exact E. }
  assert (Hsv : Znth s (replace_Znth s nb (replace_Znth q na col)) 0 = nb).
  { apply Znth_replace_Znth_Same. exact Hs'. }
  split.
  - intros [HP|[Hvb|Hva]].
    + destruct (proj1 (Hfaith v Hv) HP) as [j [Hjlo [Hjhi Hjv]]].
      destruct (Hdistinct j Hjlo Hjhi) as [Hjq Hjs].
      assert (Hjidx : 0 <= j < Zlength col) by lia.
      assert (Hjidx' : 0 <= j < Zlength (replace_Znth q na col)).
      { rewrite Zlength_replace_Znth. exact Hjidx. }
      exists j. split; [exact Hjlo|]. split; [apply Hkeep; assumption|].
      rewrite Znth_replace_Znth_Diff.
      * rewrite Znth_replace_Znth_Diff.
        -- exact Hjv.
        -- exact Hq.
        -- exact Hjidx.
        -- intro E. apply Hjq. symmetry. exact E.
      * exact Hs'.
      * exact Hjidx'.
      * intro E. apply Hjs. symmetry. exact E.
    + exists q. split; [exact Hqlo|]. split; [exact Hqnew|].
      rewrite Hqv. symmetry. exact (proj2 Hvb).
    + exists s. split; [exact Hslo|]. split; [exact Hsnew|].
      rewrite Hsv. symmetry. exact (proj2 Hva).
  - intros [j [Hjlo [Hjhi Hjv]]].
    destruct (Hdecomp j Hjlo Hjhi) as [Hjq|[Hjs|Hjold]].
    + right. left. split.
      * apply (Hqsrc j Hjlo Hjhi Hjq).
      * subst j. rewrite Hqv in Hjv. symmetry. exact Hjv.
    + right. right. split.
      * apply (Hssrc j Hjlo Hjhi Hjs).
      * subst j. rewrite Hsv in Hjv. symmetry. exact Hjv.
    + left. apply (proj2 (Hfaith v Hv)). exists j.
      split; [exact Hjlo|]. split; [exact Hjold|].
      assert (Hjidx : 0 <= j < Zlength col) by lia.
      assert (Hjidx' : 0 <= j < Zlength (replace_Znth q na col)).
      { rewrite Zlength_replace_Znth. exact Hjidx. }
      rewrite Znth_replace_Znth_Diff in Hjv.
      * rewrite Znth_replace_Znth_Diff in Hjv.
        -- exact Hjv.
        -- exact Hq.
        -- exact Hjidx.
        -- destruct (Hdistinct j Hjlo Hjold) as [Hjq Hjs].
           intro E. apply Hjq. symmetry. exact E.
      * exact Hs'.
      * exact Hjidx'.
      * destruct (Hdistinct j Hjlo Hjold) as [Hjq Hjs].
        intro E. apply Hjs. symmetry. exact E.
Qed.


Lemma twosat_prefix_reverse_edge_succ_r19_probe :
  forall (i : Z) (lit1_l lit2_l : list Z) (a b na nb va vb u v : Z),
    0 <= i ->
    a = Znth i lit1_l 0 -> b = Znth i lit2_l 0 ->
    twosat_clause_encoding a b na nb va vb ->
    twosat_clause_reverse a b vb na ->
    twosat_clause_reverse a b va nb ->
    (twosat_prefix_reverse_edge i lit1_l lit2_l u v \/
      (u = vb /\ v = na) \/ (u = va /\ v = nb)) <->
    twosat_prefix_reverse_edge (i + 1) lit1_l lit2_l u v.
Proof.
  intros i l1 l2 a b na nb va vb u v Hi Ha Hb Henc Hna Hnb.
  destruct Henc as [Hna0 [Hnb0 [Hva0 Hvb0]]].
  split.
  - intros [Hold|[Hnewa|Hnewb]].
    + destruct Hold as [k [Hk0 [Hki Hcl]]].
      exists k. repeat split; try assumption; lia.
    + destruct Hnewa as [Hu Hv]. subst u. subst v.
      exists i. split; [lia|]. split; [lia|].
      rewrite <- Ha, <- Hb. exact Hna.
    + destruct Hnewb as [Hu Hv]. subst u. subst v.
      exists i. split; [lia|]. split; [lia|].
      rewrite <- Ha, <- Hb. exact Hnb.
  - intros [k [Hk0 [Hkhi Hcl]]].
    destruct (Z.lt_trichotomy k i) as [Hlt|[Heq|Hgt]].
    + left. exists k. repeat split; assumption.
    + subst k. right.
      rewrite <- Ha, <- Hb in Hcl.
      unfold twosat_clause_reverse, twosat_clause_forward in Hcl.
      destruct Hcl as [[Hv Hu]|[Hv Hu]].
      * left. split.
        -- exact (eq_trans Hu (eq_sym Hvb0)).
        -- exact (eq_trans Hv (eq_sym Hna0)).
      * right. split.
        -- exact (eq_trans Hu (eq_sym Hva0)).
        -- exact (eq_trans Hv (eq_sym Hnb0)).
    + exfalso; lia.
Qed.


(* r13 independent graph/SAT bridge, accepted by annotation quality gate. *)
(* Pure bridge only: this scratch file does not model a CSR update or DFS. *)
Definition literal_to_vertex_r8 (l : TwoSAT.literal) : Z :=
  (fst l - 1) * 2 + if snd l then 0 else 1.

Definition vertex_to_literal_r8 (u : Z) : TwoSAT.literal :=
  (u / 2 + 1, Z.even u).

Definition twosat_c_literal_r8 (a : Z) : TwoSAT.literal :=
  (Z.abs a, if Z.ltb 0 a then true else false).

Definition twosat_formula_r8 (m : Z) (lit1_l lit2_l : list Z) : TwoSAT.formula :=
  map (fun k => (twosat_c_literal_r8 (Znth (Z.of_nat k) lit1_l 0),
                 twosat_c_literal_r8 (Znth (Z.of_nat k) lit2_l 0)))
      (seq 0 (Z.to_nat m)).

Lemma literal_to_vertex_range_r8 : forall n l,
  TwoSAT.valid_literal n l -> 0 <= literal_to_vertex_r8 l < 2 * n.
Proof.
  intros n [v b] Hv. unfold TwoSAT.valid_literal in Hv. simpl in Hv.
  unfold literal_to_vertex_r8. cbn [fst snd]. destruct b; lia.
Qed.


Lemma vertex_to_literal_valid_r8 : forall n u,
  0 <= u < 2 * n -> TwoSAT.valid_literal n (vertex_to_literal_r8 u).
Proof.
  intros n u Hu. unfold vertex_to_literal_r8, TwoSAT.valid_literal. simpl.
  split.
  - assert (0 <= u / 2) by (apply Z.div_pos; lia). lia.
  - assert (u / 2 < n) by (apply Z.div_lt_upper_bound; lia). lia.
Qed.

Lemma literal_vertex_roundtrip_r8 : forall n l,
  TwoSAT.valid_literal n l -> vertex_to_literal_r8 (literal_to_vertex_r8 l) = l.
Proof.
  intros n [v b] Hv. unfold TwoSAT.valid_literal in Hv. simpl in Hv.
  unfold vertex_to_literal_r8, literal_to_vertex_r8. cbn [fst snd].
  destruct b.
  - assert (Hq : ((v - 1) * 2) / 2 = v - 1).
    { apply Z.div_mul; lia. }
    rewrite Z.add_0_r. rewrite Hq. rewrite Z.even_mul, Z.even_2. simpl. f_equal; lia.
  - assert (Hq : ((v - 1) * 2 + 1) / 2 = v - 1).
    { symmetry. apply (Z.div_unique ((v - 1) * 2 + 1) 2 (v - 1) 1); [left; split; lia | ring]. }
    rewrite Hq. replace (Z.even ((v - 1) * 2 + 1)) with false.
    + f_equal; lia.
    + rewrite Z.add_comm, Z.mul_comm.
      rewrite Z.even_add_mul_even with (n := 1) (m := 2) (p := (v - 1)); [reflexivity | exists 1; ring].
Qed.

Lemma vertex_decode_encode_r8 : forall n u,
  0 <= u < 2 * n -> literal_to_vertex_r8 (vertex_to_literal_r8 u) = u.
Proof.
  intros n u Hu. unfold literal_to_vertex_r8, vertex_to_literal_r8; simpl.
  destruct (Z.even u) eqn: He.
  - apply Z.even_spec in He. destruct He as [k Hk]. subst u.
    rewrite (Z.mul_comm 2 k), Z.div_mul by lia.
    replace (Z.even (2 * k)) with true by
      (symmetry; apply Z.even_spec; exists k; lia). lia.
  - destruct (Z.Even_or_Odd u) as [HE|HO].
    + pose proof (proj2 (Z.even_spec u) HE) as Ht. rewrite Ht in He. discriminate.
    + destruct HO as [k Hk]. subst u.
      assert (Hd : (2 * k + 1) / 2 = k).
      { symmetry. apply (Z.div_unique (2 * k + 1) 2 k 1); [left; split; lia|lia]. }
      rewrite Hd. lia.
Qed.

Lemma twosat_c_literal_valid_r8 : forall n a,
  1 <= Z.abs a <= n -> TwoSAT.valid_literal n (twosat_c_literal_r8 a).
Proof. intros; unfold twosat_c_literal_r8, TwoSAT.valid_literal; simpl; exact H. Qed.

(* This is the compile-gated r5 formula-validity proof, copied unchanged
   modulo the r8 names. *)
Lemma twosat_formula_valid_r8 : forall n m lit1_l lit2_l,
  twosat_clause_input_wf n m lit1_l lit2_l ->
  TwoSAT.valid_formula n (twosat_formula_r8 m lit1_l lit2_l).
Proof.
  intros n m l1 l2 Hw c Hin. unfold twosat_formula_r8 in Hin.
  apply in_map_iff in Hin. destruct Hin as [k [Hc Hk]]. subst c.
  apply in_seq in Hk. destruct Hw as [_ [_ [Hl1 [Hl2 Hrange]]]].
  split; apply twosat_c_literal_valid_r8.
  - apply Hrange. split.
    + lia.
    + apply (proj2 (Z2Nat.inj_lt (Z.of_nat k) m ltac:(lia) ltac:(lia))).
      rewrite Nat2Z.id. exact (proj2 Hk).
  - apply Hrange. split.
    + lia.
    + apply (proj2 (Z2Nat.inj_lt (Z.of_nat k) m ltac:(lia) ltac:(lia))).
      rewrite Nat2Z.id. exact (proj2 Hk).
Qed.

Lemma decode_c_literal_r8 : forall a,
  a <> 0 -> vertex_to_literal_r8 (lit_to_vertex a) =
    (Z.abs a, Z.geb a 0).
Proof.
  intros a Ha. unfold vertex_to_literal_r8, lit_to_vertex.
  destruct (Z.ltb a 0) eqn:Hlt.
  - apply Z.ltb_lt in Hlt. rewrite Z.abs_neq by lia.
    assert (Hd : (2 * (- a - 1) + 1) / 2 = -a - 1).
    { symmetry. apply (Z.div_unique (2 * (-a-1)+1) 2 (-a-1) 1); [left; split; lia|lia]. }
    rewrite Hd. replace (Z.even (2 * (-a-1)+1)) with false.
    + destruct (Z.geb a 0) eqn:Hg; [apply Z.geb_le in Hg; lia|f_equal; lia].
    + symmetry. apply Z.even_odd.
  - apply Z.ltb_ge in Hlt. rewrite Z.abs_eq by lia.
    assert (Hd : (2 * (a - 1)) / 2 = a - 1).
    { symmetry. apply (Z.div_unique (2 * (a-1)) 2 (a-1) 0); [left; split; lia|lia]. }
    rewrite Z.add_0_r. rewrite Hd. replace (Z.even (2 * (a-1))) with true.
    + destruct (Z.geb a 0) eqn:Hg; [f_equal; lia|
        assert (Ht : Z.geb a 0 = true) by (apply Z.geb_le; lia); rewrite Ht in Hg; discriminate].
    + symmetry. apply Z.even_spec. exists (a-1). lia.
Qed.

Lemma decode_c_neg_literal_r8 : forall a,
  a <> 0 -> vertex_to_literal_r8 (neg_vertex a) =
    TwoSAT.negate (Z.abs a, Z.geb a 0).
Proof.
  intros a Ha. unfold neg_vertex. rewrite decode_c_literal_r8 by lia.
  rewrite Z.abs_opp. unfold TwoSAT.negate; simpl.
  destruct (Z.geb a 0) eqn:Hg; destruct (Z.geb (-a) 0) eqn:Hg'; try reflexivity.
  - apply Z.geb_le in Hg. apply Z.geb_le in Hg'. lia.
  - assert (Ht : Z.geb a 0 = true) by (apply Z.geb_le; lia); rewrite Ht in Hg; discriminate.
Qed.

Lemma c_literal_encode_r8 : forall a,
  a <> 0 -> literal_to_vertex_r8 (Z.abs a, Z.geb a 0) = lit_to_vertex a.
Proof.
  intros a Ha. unfold literal_to_vertex_r8, lit_to_vertex.
  destruct (Z.ltb a 0) eqn:Hlt.
  - apply Z.ltb_lt in Hlt. rewrite Z.abs_neq by lia.
    destruct (Z.geb a 0) eqn:Hg; [apply Z.geb_le in Hg; lia|
      change ((-a - 1) * 2 + 1 = 2 * (-a - 1) + 1); ring].
  - apply Z.ltb_ge in Hlt. rewrite Z.abs_eq by lia.
    destruct (Z.geb a 0) eqn:Hg; [
      change ((a - 1) * 2 + 0 = 2 * (a - 1) + 0); ring|
      assert (Ht : Z.geb a 0 = true) by (apply Z.geb_le; lia); rewrite Ht in Hg; discriminate].
Qed.

Lemma c_neg_literal_encode_r8 : forall a,
  a <> 0 -> literal_to_vertex_r8 (TwoSAT.negate (Z.abs a, Z.geb a 0)) = neg_vertex a.
Proof.
  intros a Ha. unfold neg_vertex, literal_to_vertex_r8, lit_to_vertex, TwoSAT.negate; simpl.
  destruct (Z.ltb a 0) eqn:Hlt.
  - apply Z.ltb_lt in Hlt. rewrite Z.abs_neq by lia.
    destruct (Z.geb a 0) eqn:Hg; [apply Z.geb_le in Hg; lia|].
    rewrite Z.abs_opp. assert (Ho : Z.ltb (-a) 0 = false) by (apply Z.ltb_ge; lia).
    rewrite Ho. rewrite Z.abs_neq by lia. cbn.
    change ((-a - 1) * 2 + 0 = 2 * (-a - 1) + 0); ring.
  - apply Z.ltb_ge in Hlt. rewrite Z.abs_eq by lia.
    destruct (Z.geb a 0) eqn:Hg; [|assert (Ht : Z.geb a 0 = true) by (apply Z.geb_le; lia); rewrite Ht in Hg; discriminate].
    rewrite Z.abs_opp. assert (Ho : Z.ltb (-a) 0 = true) by (apply Z.ltb_lt; lia).
    rewrite Ho. rewrite Z.abs_eq by lia. cbn.
    change ((a - 1) * 2 + 1 = 2 * (a - 1) + 1); ring.
Qed.

Lemma twosat_c_literal_normalize_r8 : forall a,
  a <> 0 -> twosat_c_literal_r8 a = (Z.abs a, Z.geb a 0).
Proof.
  intros a Ha. unfold twosat_c_literal_r8.
  destruct (Z.ltb 0 a) eqn: Hp; destruct (Z.geb a 0) eqn: Hg; try reflexivity.
  - apply Z.ltb_lt in Hp.
    assert (Ht : Z.geb a 0 = true) by (apply Z.geb_le; lia).
    rewrite Ht in Hg; discriminate.
  - apply Z.ltb_ge in Hp. apply Z.geb_le in Hg. lia.
Qed.

Lemma twosat_formula_clause_in_r8 : forall m lit1_l lit2_l (k : Z),
  0 <= k < m ->
  In (twosat_c_literal_r8 (Znth k lit1_l 0),
      twosat_c_literal_r8 (Znth k lit2_l 0))
     (twosat_formula_r8 m lit1_l lit2_l).
Proof.
  intros m l1 l2 k Hk. unfold twosat_formula_r8.
  apply in_map_iff. exists (Z.to_nat k). split.
  - rewrite Z2Nat.id by lia. reflexivity.
  - apply in_seq. split; [lia|].
    apply (proj1 (Z2Nat.inj_lt k m ltac:(lia) ltac:(lia))). exact (proj2 Hk).
Qed.

Lemma twosat_formula_length_r8 : forall m lit1_l lit2_l,
  0 <= m -> Zlength (twosat_formula_r8 m lit1_l lit2_l) = m.
Proof.
  intros. unfold twosat_formula_r8. rewrite Zlength_correct, length_map, length_seq, Z2Nat.id by lia. reflexivity.
Qed.

(* The central one-step representation equivalence.  The reverse direction
   opens the DiGraph edge identifier and recovers its source formula clause;
   it is not an appeal to an SCC or SAT theorem. *)
Lemma twosat_canonical_step_iff_implication_r8 : forall n m lit1_l lit2_l u v
  (Hw : twosat_clause_input_wf n m lit1_l lit2_l),
  0 <= u < 2 * n -> 0 <= v < 2 * n ->
  @step AdjGraph Z (Z * Z) AdjGraph_graph
      (twosat_canonical_graph n m lit1_l lit2_l) u v <->
  step (TwoSAT.implication_graph (twosat_formula_r8 m lit1_l lit2_l) n
          (twosat_formula_valid_r8 n m lit1_l lit2_l Hw))
       (vertex_to_literal_r8 u) (vertex_to_literal_r8 v).
Proof.
  intros n m l1 l2 u v Hw Hu Hv.
  destruct Hw as [Hn [Hm [Hl1 [Hl2 Hlit]]]].
  assert (Hw' : twosat_clause_input_wf n m l1 l2).
  { exact (conj Hn (conj Hm (conj Hl1 (conj Hl2 Hlit)))). }
  split.
  - intro Hstep.
    apply (proj1 (twosat_step_canonical_forward n m l1 l2 u v Hw' Hu Hv)) in Hstep.
    apply (proj1 (twosat_forward_row_membership n m l1 l2 u v Hw')) in Hstep.
    destruct Hstep as [k [Hk0 [Hkm Hedge]]].
    assert (Ha : Znth k l1 0 <> 0).
    { intro E. pose proof (Hlit k (conj Hk0 Hkm)) as R. rewrite E in R. simpl in R. lia. }
    assert (Hb : Znth k l2 0 <> 0).
    { intro E. pose proof (Hlit k (conj Hk0 Hkm)) as R. rewrite E in R. simpl in R. lia. }
    assert (Hcl : In (twosat_c_literal_r8 (Znth k l1 0), twosat_c_literal_r8 (Znth k l2 0))
      (twosat_formula_r8 m l1 l2)).
    { apply twosat_formula_clause_in_r8; lia. }
    pose proof (TwoSAT.step_implication (twosat_formula_r8 m l1 l2) n
      (twosat_formula_valid_r8 n m l1 l2 (conj Hn (conj Hm (conj Hl1 (conj Hl2 Hlit)))))
      (twosat_c_literal_r8 (Znth k l1 0), twosat_c_literal_r8 (Znth k l2 0)) Hcl) as Himp.
    destruct Hedge as [[Eu Ev]|[Eu Ev]]; subst u; subst v.
    + rewrite decode_c_neg_literal_r8 by exact Ha.
      rewrite decode_c_literal_r8 by exact Hb.
      rewrite !twosat_c_literal_normalize_r8 in Himp by assumption.
      exact (proj1 Himp).
    + rewrite decode_c_neg_literal_r8 by exact Hb.
      rewrite decode_c_literal_r8 by exact Ha.
      rewrite !twosat_c_literal_normalize_r8 in Himp by assumption.
      exact (proj2 Himp).
  - intro Hstep.
    destruct Hstep as [e [He Hsrc Hdst Hfst Hsnd]].
    unfold TwoSAT.implication_graph in He, Hfst, Hsnd; simpl in He, Hfst, Hsnd.
    assert (Hflen : Zlength (twosat_formula_r8 m l1 l2) = m).
    { apply twosat_formula_length_r8; lia. }
    assert (He' : 0 <= e < 2 * m).
    { rewrite <- Hflen; exact He. }
    assert (Hk : 0 <= e / 2 < Zlength (twosat_formula_r8 m l1 l2)).
    { rewrite Hflen. split; [apply Z.div_pos; lia|apply Z.div_lt_upper_bound; lia]. }
    assert (Hin : In (TwoSAT.nth_clause (twosat_formula_r8 m l1 l2) (e / 2))
      (twosat_formula_r8 m l1 l2)).
    { apply TwoSAT.nth_clause_in; exact Hk. }
    unfold twosat_formula_r8 in Hin.
    apply in_map_iff in Hin. destruct Hin as [j [Hcl Hj]].
    apply in_seq in Hj.
    assert (Hj0 : 0 <= Z.of_nat j < m).
    { split; [lia|]. apply (proj2 (Z2Nat.inj_lt (Z.of_nat j) m ltac:(lia) ltac:(lia))).
      rewrite Nat2Z.id. exact (proj2 Hj). }
    assert (Ha : Znth (Z.of_nat j) l1 0 <> 0).
    { intro E. pose proof (Hlit (Z.of_nat j) Hj0) as R. rewrite E in R. simpl in R. lia. }
    assert (Hb : Znth (Z.of_nat j) l2 0 <> 0).
    { intro E. pose proof (Hlit (Z.of_nat j) Hj0) as R. rewrite E in R. simpl in R. lia. }
    apply (proj2 (twosat_step_canonical_forward n m l1 l2 u v Hw' Hu Hv)).
    apply (proj2 (twosat_forward_row_membership n m l1 l2 u v Hw')).
    exists (Z.of_nat j). split; [exact (proj1 Hj0)|].
    split; [exact (proj2 Hj0)|].
    unfold twosat_clause_forward.
    change
      ((if Z.even e then TwoSAT.negate (fst (TwoSAT.nth_clause (twosat_formula_r8 m l1 l2) (e / 2)))
        else TwoSAT.negate (snd (TwoSAT.nth_clause (twosat_formula_r8 m l1 l2) (e / 2)))) =
       vertex_to_literal_r8 u) in Hfst.
    change
      ((if Z.even e then snd (TwoSAT.nth_clause (twosat_formula_r8 m l1 l2) (e / 2))
        else fst (TwoSAT.nth_clause (twosat_formula_r8 m l1 l2) (e / 2))) =
       vertex_to_literal_r8 v) in Hsnd.
    unfold twosat_formula_r8 in Hfst, Hsnd.
    rewrite <- Hcl in Hfst, Hsnd.
    destruct (Z.even e) eqn: Heven.
    + left. split.
      * rewrite <- (vertex_decode_encode_r8 n u Hu).
        rewrite <- Hfst. cbn. rewrite twosat_c_literal_normalize_r8 by exact Ha.
        apply c_neg_literal_encode_r8; exact Ha.
      * rewrite <- (vertex_decode_encode_r8 n v Hv).
        rewrite <- Hsnd. cbn. rewrite twosat_c_literal_normalize_r8 by exact Hb.
        apply c_literal_encode_r8; exact Hb.
    + right. split.
      * rewrite <- (vertex_decode_encode_r8 n u Hu).
        rewrite <- Hfst. cbn. rewrite twosat_c_literal_normalize_r8 by exact Hb.
        apply c_neg_literal_encode_r8; exact Hb.
      * rewrite <- (vertex_decode_encode_r8 n v Hv).
        rewrite <- Hsnd. cbn. rewrite twosat_c_literal_normalize_r8 by exact Ha.
        apply c_literal_encode_r8; exact Ha.
Qed.


(* Fresh r10 nsteps transport experiments follow. *)

Lemma twosat_path_forward_r10 : forall n m l1 l2 u v
  (Hw : twosat_clause_input_wf n m l1 l2),
  0 <= u < 2*n -> 0 <= v < 2*n ->
  reachable (twosat_canonical_graph n m l1 l2) u v ->
  reachable (TwoSAT.implication_graph (twosat_formula_r8 m l1 l2) n
    (twosat_formula_valid_r8 n m l1 l2 Hw))
    (vertex_to_literal_r8 u) (vertex_to_literal_r8 v).
Proof.
  intros n m l1 l2 u v Hw Hu Hv H.
  unfold reachable, clos_refl_trans in H.
  destruct H as [k H].
  revert u v Hu Hv H.
  induction k as [|k IH]; intros u v Hu Hv H.
  - simpl in H. change (u = v) in H. subst v. reflexivity.
  - simpl in H. destruct H as [w [Huw Hwv]].
    destruct Huw as [e [He [Hu' [Hw' Hin]]]].
    eapply reachable_trans.
    + apply step_rt.
      apply (proj1 (twosat_canonical_step_iff_implication_r8 n m l1 l2 u w Hw Hu Hw')).
      exact (ex_intro (fun e => adj_step_aux (twosat_canonical_graph n m l1 l2) e u w)
        e (conj He (conj Hu' (conj Hw' Hin)))).
    + apply IH with (u:=w); assumption.
Qed.

Lemma twosat_path_backward_r10 : forall n m l1 l2 u v
  (Hw : twosat_clause_input_wf n m l1 l2),
  0 <= u < 2*n -> 0 <= v < 2*n ->
  reachable (TwoSAT.implication_graph (twosat_formula_r8 m l1 l2) n
    (twosat_formula_valid_r8 n m l1 l2 Hw))
    (vertex_to_literal_r8 u) (vertex_to_literal_r8 v) ->
  reachable (twosat_canonical_graph n m l1 l2) u v.
Proof.
  intros n m l1 l2 u v Hw Hu Hv H.
  unfold reachable, clos_refl_trans in H.
  destruct H as [k H].
  pose (Hform := twosat_formula_valid_r8 n m l1 l2 Hw).
  assert (Hdecodeu : TwoSAT.valid_literal n (vertex_to_literal_r8 u)).
  { apply vertex_to_literal_valid_r8; exact Hu. }
  assert (Hdecodev : TwoSAT.valid_literal n (vertex_to_literal_r8 v)).
  { apply vertex_to_literal_valid_r8; exact Hv. }
  rewrite <- (vertex_decode_encode_r8 n u Hu),
          <- (vertex_decode_encode_r8 n v Hv).
  revert Hdecodeu Hdecodev H.
  generalize (vertex_to_literal_r8 u) as x.
  generalize (vertex_to_literal_r8 v) as y.
  induction k as [|k IH]; intros y x Hx Hy Hpath.
  - simpl in Hpath. change (x = y) in Hpath. subst y. reflexivity.
  - simpl in Hpath. destruct Hpath as [w [Hxw Hwy]].
    unfold step in Hxw. destruct Hxw as [e Hxw].
    change (TwoSAT.dig_step_aux
      (TwoSAT.implication_graph (twosat_formula_r8 m l1 l2) n Hform) e x w) in Hxw.
    unfold SetsDomain.Sets.lift1 in Hwy.
    destruct Hxw as [He Hx' Hw' Hfst Hsnd].
    change (TwoSAT.valid_literal n x) in Hx'.
    change (TwoSAT.valid_literal n w) in Hw'.
    eapply reachable_trans.
    + apply step_rt.
      apply (proj2 (twosat_canonical_step_iff_implication_r8 n m l1 l2
        (literal_to_vertex_r8 x) (literal_to_vertex_r8 w) Hw
        (literal_to_vertex_range_r8 n x Hx')
        (literal_to_vertex_range_r8 n w Hw'))).
      rewrite (literal_vertex_roundtrip_r8 n x Hx'),
              (literal_vertex_roundtrip_r8 n w Hw').
      exists e. exact (@DigStepAux TwoSAT.literal Z _ e x w He Hx' Hw' Hfst Hsnd).
    + apply IH with (x:=w); assumption.
Qed.

Lemma twosat_mutually_reachable_iff_r10 : forall n m l1 l2 u v
  (Hw : twosat_clause_input_wf n m l1 l2),
  0 <= u < 2*n -> 0 <= v < 2*n ->
  (reachable (twosat_canonical_graph n m l1 l2) u v /\
   reachable (twosat_canonical_graph n m l1 l2) v u) <->
  TwoSAT.mutually_reachable (TwoSAT.implication_graph (twosat_formula_r8 m l1 l2) n
    (twosat_formula_valid_r8 n m l1 l2 Hw))
    (vertex_to_literal_r8 u) (vertex_to_literal_r8 v).
Proof.
  intros n m l1 l2 u v Hw Hu Hv.
  unfold TwoSAT.mutually_reachable; split; intros [Huv Hvu]; split.
  - apply twosat_path_forward_r10 with (n:=n) (m:=m) (l1:=l1) (l2:=l2) (Hw:=Hw); assumption.
  - apply twosat_path_forward_r10 with (n:=n) (m:=m) (l1:=l1) (l2:=l2) (Hw:=Hw); assumption.
  - apply twosat_path_backward_r10 with (n:=n) (m:=m) (l1:=l1) (l2:=l2) (Hw:=Hw); assumption.
  - apply twosat_path_backward_r10 with (n:=n) (m:=m) (l1:=l1) (l2:=l2) (Hw:=Hw); assumption.
Qed.
Definition sid_matches_graph_r11 (sid_l : list Z) (g : AdjGraph) (n : Z) : Prop :=
  forall u v, 0 <= u < n -> 0 <= v < n ->
    (Znth u sid_l 0 = Znth v sid_l 0 <->
     reachable g u v /\ reachable g v u).

(* C-facing spelling of the high-level Kosaraju postcondition, fixed to
   the concrete implication graph determined by the input clauses. *)
Definition sid_matches_twosat_r13 (sid_l : list Z) (n m : Z)
  (lit1_l lit2_l : list Z) : Prop :=
  sid_matches_graph_r11 sid_l (twosat_canonical_graph n m lit1_l lit2_l) (2 * n).

Lemma sid_no_conflict_iff_twosat_no_conflict_r11 : forall n m l1 l2 sid_l
  (Hw : twosat_clause_input_wf n m l1 l2),
  sid_matches_graph_r11 sid_l (twosat_canonical_graph n m l1 l2) (2*n) ->
  (no_conflict_by_sid sid_l n <->
   TwoSAT.no_conflict (TwoSAT.implication_graph (twosat_formula_r8 m l1 l2) n
     (twosat_formula_valid_r8 n m l1 l2 Hw)) n).
Proof.
  intros n m l1 l2 sid_l Hw Hsid.
  unfold no_conflict_by_sid, TwoSAT.no_conflict.
  split.
  - intros Hnc v Hv Hmut.
    apply (Hnc v Hv).
    apply (proj2 (Hsid (2*(v-1)) (2*(v-1)+1) ltac:(lia) ltac:(lia))).
    apply (proj2 (twosat_mutually_reachable_iff_r10 n m l1 l2
      (2*(v-1)) (2*(v-1)+1) Hw ltac:(lia) ltac:(lia))).
    assert (HdecT : vertex_to_literal_r8 (2 * (v - 1)) = (v, true)).
    { replace (2 * (v - 1)) with (literal_to_vertex_r8 (v, true)) by
        (unfold literal_to_vertex_r8; cbn [fst snd]; ring).
      apply (literal_vertex_roundtrip_r8 n (v, true)). unfold TwoSAT.valid_literal; simpl; exact Hv. }
    assert (HdecF : vertex_to_literal_r8 (2 * (v - 1) + 1) = (v, false)).
    { replace (2 * (v - 1) + 1) with (literal_to_vertex_r8 (v, false)) by
        (unfold literal_to_vertex_r8; cbn [fst snd]; ring).
      apply (literal_vertex_roundtrip_r8 n (v, false)). unfold TwoSAT.valid_literal; simpl; exact Hv. }
    rewrite HdecT, HdecF.
    exact Hmut.
(*    unfold vertex_to_literal_r8 in Hmut; simpl in Hmut.
    assert (Hdiv : (2 * (v - 1)) / 2 + 1 = v) by lia.
    assert (Hdiv' : (2 * (v - 1) + 1) / 2 + 1 = v) by
      (symmetry; apply (Z.div_unique (2 * (v - 1) + 1) 2 (v - 1) 1); [left; split; lia|lia]).
    rewrite Hdiv, Hdiv' in Hmut.
    replace (Z.even (2 * (v - 1))) with true in Hmut by
      (symmetry; apply Z.even_spec; exists (v-1); lia).
    replace (Z.even (2 * (v - 1) + 1)) with false in Hmut by
      (symmetry; apply Z.even_odd).
    exact Hmut. *)
  - intros Hnc v Hv Hsame.
    apply (Hnc v Hv).
    assert (Hgraph : reachable (twosat_canonical_graph n m l1 l2) (2*(v-1)) (2*(v-1)+1) /\
                     reachable (twosat_canonical_graph n m l1 l2) (2*(v-1)+1) (2*(v-1))).
    { apply (proj1 (Hsid (2*(v-1)) (2*(v-1)+1) ltac:(lia) ltac:(lia))). exact Hsame. }
    pose proof (proj1 (twosat_mutually_reachable_iff_r10 n m l1 l2
      (2*(v-1)) (2*(v-1)+1) Hw ltac:(lia) ltac:(lia)) Hgraph) as Htrans.
    assert (HdecT : vertex_to_literal_r8 (2 * (v - 1)) = (v, true)).
    { replace (2 * (v - 1)) with (literal_to_vertex_r8 (v, true)) by
        (unfold literal_to_vertex_r8; cbn [fst snd]; ring).
      apply (literal_vertex_roundtrip_r8 n (v, true)). unfold TwoSAT.valid_literal; simpl; exact Hv. }
    assert (HdecF : vertex_to_literal_r8 (2 * (v - 1) + 1) = (v, false)).
    { replace (2 * (v - 1) + 1) with (literal_to_vertex_r8 (v, false)) by
        (unfold literal_to_vertex_r8; cbn [fst snd]; ring).
      apply (literal_vertex_roundtrip_r8 n (v, false)). unfold TwoSAT.valid_literal; simpl; exact Hv. }
    rewrite HdecT, HdecF in Htrans. exact Htrans.
Qed.

Lemma sid_no_conflict_iff_satisfiable_r11 : forall n m l1 l2 sid_l,
  twosat_clause_input_wf n m l1 l2 ->
  sid_matches_graph_r11 sid_l (twosat_canonical_graph n m l1 l2) (2*n) ->
  (no_conflict_by_sid sid_l n <-> TwoSAT.satisfiable (twosat_formula_r8 m l1 l2)).
Proof.
  intros n m l1 l2 sid_l Hw Hsid.
  rewrite (sid_no_conflict_iff_twosat_no_conflict_r11 n m l1 l2 sid_l Hw Hsid).
  symmetry. apply (TwoSAT.two_sat_characterization
    (twosat_formula_r8 m l1 l2) n (twosat_formula_valid_r8 n m l1 l2 Hw)).
Qed.

(* The externally visible return convention; it is a declarative SAT
   property, not a model of CSR construction or DFS. *)
Definition twosat_return_contract_r12 (n m : Z) (lit1_l lit2_l : list Z)
  (result : Z) : Prop :=
  (result = 0 <-> TwoSAT.satisfiable (twosat_formula_r8 m lit1_l lit2_l)) /\
  (result = 1 <-> ~ TwoSAT.satisfiable (twosat_formula_r8 m lit1_l lit2_l)).

(* This abstracts only the result of the caller's conflict scan.  It does
   not encode CSR construction, DFS, or the loop's operational steps. *)
Definition twosat_conflict_scan_result_r13
  (sid_l : list Z) (n result : Z) : Prop :=
  (result = 0 \/ result = 1) /\
  (result = 0 -> no_conflict_by_sid sid_l n) /\
  (result = 1 -> ~ no_conflict_by_sid sid_l n).

Lemma twosat_conflict_scan_return_contract_r13 :
  forall n m lit1_l lit2_l sid_l result,
    twosat_clause_input_wf n m lit1_l lit2_l ->
    sid_matches_twosat_r13 sid_l n m lit1_l lit2_l ->
    twosat_conflict_scan_result_r13 sid_l n result ->
    twosat_return_contract_r12 n m lit1_l lit2_l result.
Proof.
  intros n m lit1_l lit2_l sid_l result Hinput Hsid [Hresult [Hzero Hone]].
  pose proof (sid_no_conflict_iff_satisfiable_r11 n m lit1_l lit2_l sid_l
    Hinput Hsid) as Hsat.
  unfold twosat_return_contract_r12.
  split.
  - split.
    + intro H0. apply (proj1 Hsat). apply Hzero. exact H0.
    + intro HS. destruct Hresult as [H0 | H1].
      * exact H0.
      * exfalso. apply (Hone H1). apply (proj2 Hsat). exact HS.
  - split.
    + intros H1 HS. apply (Hone H1). apply (proj2 Hsat). exact HS.
    + intro HNS. destruct Hresult as [H0 | H1].
      * exfalso. apply HNS. apply (proj1 Hsat). apply Hzero. exact H0.
      * exact H1.
Qed.
