Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Lia.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap relations.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Import naive_C_Rules.
Import ListNotations.
Local Open Scope string.
Local Open Scope list.

From FP Require Import SetsFixedpoints PartialOrder_Setoid BourbakiWitt.
From GraphLib Require Import graph_basic reachable_basic.
From MonadLib.MonadErr Require Import MonadErrBasic MonadErrHoare MonadErrLoop
                               MonadErrHoarePartial monadesafe_lib.
From Algorithms Require Import Kosaraju.Kosaraju Kosaraju.SCC.
(* Re-import GraphLib's reachable_basic AFTER the MonadErr imports so that the
   graph step (G -> V -> V -> Prop) stays in scope; MonadErrBasic's Section
   monadop also declares a `step : Type` that would otherwise shadow it. *)
From GraphLib Require Import reachable_basic.
Export MonadNotation.
Local Open Scope monad.
Local Open Scope order_scope.
(* Re-open Z_scope AFTER order_scope so that `<=`/`>=` on Z keep resolving to
   Z.le/Z.ge (order_scope defines `<=` as the Order typeclass `order_rel`,
   which would otherwise shadow Z comparisons).  Program equivalence keeps
   using the order_scope `==` notation via the type-based disambiguation. *)
Local Open Scope Z_scope.
Local Open Scope sac.

(* ================================================================= *)
(* Adjacency-list graph carrier (directed, abstract).                *)
(*   adj_fwd !! u = forward (out) neighbours of u                    *)
(*   adj_rev !! u = reversed (in) neighbours of u                    *)
(*   This is the abstract graph the Kosaraju monad reasons about.    *)
(*   The C side stores the same graph in CSR layout (adj_col +       *)
(*   adj_row); the refinement relates the CSR arrays to adj_rev.     *)
(* ================================================================= *)

Record AdjGraph := MkAdjGraph {
  adj_verts : Z;
  adj_fwd   : list (list Z);
  adj_rev   : list (list Z);
}.

Definition adj_vvalid (g : AdjGraph) (v : Z) : Prop :=
  (0 <= v < adj_verts g)%Z.

Definition adj_evalid (g : AdjGraph) (e : Z * Z) : Prop :=
  let (u, v) := e in adj_vvalid g u /\ adj_vvalid g v.

Definition adj_step_aux (g : AdjGraph) (e : Z * Z) (x y : Z) : Prop :=
  e = (x, y) /\
  adj_vvalid g x /\
  adj_vvalid g y /\
  In y (nth (Z.to_nat x) (adj_fwd g) nil).

(* gvalid: well-formed adjacency list. *)
Definition AdjGraphValid (g : AdjGraph) : Prop :=
  (Zlength (adj_fwd g) = adj_verts g)%Z /\
  (Zlength (adj_rev g) = adj_verts g)%Z /\
  (forall u, (0 <= u < adj_verts g)%Z ->
    forall v, In v (nth (Z.to_nat u) (adj_fwd g) nil) -> (0 <= v < adj_verts g)%Z) /\
  (forall u, (0 <= u < adj_verts g)%Z ->
    forall v, In v (nth (Z.to_nat u) (adj_rev g) nil) -> (0 <= v < adj_verts g)%Z) /\
  (forall u v,
    In v (nth (Z.to_nat u) (adj_fwd g) nil) <->
    In u (nth (Z.to_nat v) (adj_rev g) nil)).

(* ================================================================= *)
(* Graph type-class instances for AdjGraph.                          *)
(* ================================================================= *)

#[export] Instance AdjGraph_graph : Graph AdjGraph Z (Z * Z) := {|
  graph_basic.vvalid   := adj_vvalid;
  graph_basic.evalid   := adj_evalid;
  graph_basic.step_aux := adj_step_aux;
|}.


#[export] Instance AdjGraph_gvalid : GValid AdjGraph := AdjGraphValid.

#[export] Instance AdjGraph_stepvalid : StepValid AdjGraph Z (Z * Z).
Proof.
  constructor; intros g e x y Hstep.
  - destruct Hstep as [_ [Hvx [_ _]]]. exact Hvx.
  - destruct Hstep as [_ [_ [Hvy _]]]. exact Hvy.
  - destruct Hstep as [Heq [Hvx [Hvy _]]]. subst e.
    unfold adj_evalid. simpl. split; assumption.
Defined.

#[export] Instance AdjGraph_stepuniquedirected : StepUniqueDirected AdjGraph Z (Z * Z).
Proof.
  constructor; intros g e x1 y1 x2 y2 _ H1 H2.
  destruct H1 as [He1 _]. destruct H2 as [He2 _].
  rewrite He1 in He2. injection He2 as Hx Hy. subst. split; reflexivity.
Defined.

#[export] Instance AdjGraph_finitegraph : FiniteGraph AdjGraph Z (Z * Z).
Proof.
  refine {| graph_basic.listV := fun g => map Z.of_nat (seq 0 (Z.to_nat (adj_verts g))) |}.
  intros g Hg v Hv. unfold adj_vvalid in Hv.
  destruct Hv as [Hv1 Hv2].
  apply in_map_iff. exists (Z.to_nat v). split.
  - lia.
  - apply in_seq. lia.
Defined.

(* ================================================================= *)
(* Concrete KosarajuGraph packaging over AdjGraph.                   *)
(* Wraps the Section-parameterised definitions into closed,          *)
(* parameter-free symbols exportable to the C side.                  *)
(* ================================================================= *)

Definition KG : KosarajuGraph AdjGraph Z (Z * Z) :=
  {| kos_graph    := AdjGraph_graph;
     kos_gvalid   := AdjGraph_gvalid;
     kos_stepvalid := AdjGraph_stepvalid;
     kos_unique   := AdjGraph_stepuniquedirected;
     kos_finite   := AdjGraph_finitegraph;
  |}.

(* The Kosaraju abstract state, closed over V = Z. *)
Definition KSt : Type := @St Z.

(* A concrete (empty) adjacency-list graph used to instantiate the
   Section-parameterised monad programs into closed, parameter-free
   symbols.  The actual graph contents live on the C heap side; this
   carrier only carries the type-level packaging. *)
Definition empty_adj : AdjGraph := {| adj_verts := 0; adj_fwd := nil; adj_rev := nil |}.

Lemma empty_adj_valid : gvalid empty_adj.
Proof.
  unfold empty_adj.
  change (gvalid {| adj_verts := 0; adj_fwd := nil; adj_rev := nil |})
    with (AdjGraphValid {| adj_verts := 0; adj_fwd := nil; adj_rev := nil |}).
  unfold AdjGraphValid. simpl. unfold Zlength. simpl.
  split; [reflexivity|].
  split; [reflexivity|].
  split; [intros u [Hu1 Hu2] v Hv; lia|].
  split; [intros u [Hu1 Hu2] v Hv; lia|].
  intros u v. split.
  - intros Hc; destruct (Z.to_nat u); simpl in Hc; exfalso; exact Hc.
  - intros Hc; destruct (Z.to_nat v); simpl in Hc; exfalso; exact Hc.
Qed.

(* ================================================================= *)
(* Closed monad program symbols, instantiating the Section-           *)
(* parameterised DFS_finish / DFS_scc over empty_adj.  These are the  *)
(* high-level (mathematical) specs the C functions refine.            *)
(*                                                                   *)
(* Continuation forms (dfs_finish_from / dfs_scc_from) and the C-side *)
(* preconditions (pre_dfs1 / pre_dfs2) are added by the annotation    *)
(* phase (annotation_scratch_lib -> integrated here once checked).    *)
(* ================================================================= *)

Definition dfs_finish (g : AdjGraph) (u : Z) : program KSt unit :=
  @DFS_finish AdjGraph Z (Z * Z) KG g u.

Definition dfs_scc (g : AdjGraph) (root u : Z) : program KSt unit :=
  @DFS_scc AdjGraph Z (Z * Z) KG g root u.

Lemma dfs_finish_unfold : forall (g : AdjGraph) (u : Z),
  @PartialOrder_Setoid.equiv (MonadErr.M KSt unit) _
    (dfs_finish g u) (@DFS_finish_f AdjGraph Z (Z * Z) KG g (dfs_finish g) u).
Proof. intros g u. unfold dfs_finish. apply DFS_finish_unfold. Qed.

Lemma dfs_scc_unfold : forall (g : AdjGraph) (root u : Z),
  @PartialOrder_Setoid.equiv (MonadErr.M KSt unit) _
    (dfs_scc g root u) (@DFS_scc_f AdjGraph Z (Z * Z) KG g root (dfs_scc g root) u).
Proof. intros g root u. unfold dfs_scc. apply DFS_scc_unfold. Qed.

(* NOTE (SEMANTIC GAP — pending user decision): the three absorb-chain lemmas *)
(* below — dfs_scc_absorb, dfs_scc_safe_return, dfs2_return_close — used to    *)
(* close dfs2 Gap A (loop-exit `safeExec (pre_dfs2 vis sid) (ret tt) X`).      *)
(* They depended on DFS_scc_absorb inside Section Kosaraju, which was REMOVED  *)
(* in the StateRelMonad -> MonadErr refactor of Kosaraju.v, together with the  *)
(* supporting repeat_break_break_step / repeat_break_f_mono_cont infrastructure. *)
(* They had NO consumers in the current manual/auto/goal files, so they are    *)
(* deleted here to keep the lib compiling.  Re-deriving the absorb no-op       *)
(* transition (dfs_scc g root u st tt st) from current MonadErr-based          *)
(* Kosaraju.v lemmas is a semantic task: see the report.                       *)


Definition applyf {A B : Type} (f : A -> B) (a : A) := f a.

(* ================================================================= *)
(* CSR layout helpers (pure mathematical).                            *)
(*   m_of row_l      = row_l[length-1] = packed neighbour count       *)
(*   csr_lo u row_l  = row_l[u]       = start offset of u's neighbours*)
(*   csr_hi u row_l  = row_l[u+1]     = end offset of u's neighbours  *)
(* ================================================================= *)

Definition m_of (row_l : list Z) : Z :=
  Znth (Zlength row_l - 1) row_l 0.

Definition csr_lo (u : Z) (row_l : list Z) : Z :=
  Znth u row_l 0.

Definition csr_hi (u : Z) (row_l : list Z) : Z :=
  Znth (u + 1) row_l 0.

(* ================================================================= *)
(* Scoped abstract-state preconditions.                              *)
(*                                                                   *)
(* pre_dfs1 g radj_col_l radj_row_l vis1_l fin_l timer_v st :        *)
(*   relates the abstract monad state st to the CSR arrays the C     *)
(*   side owns.  vis1/fin/timer are encoded as Z lists over the      *)
(*   abstract St fields (visited1 as 0/1, finish as nat-to-Z, timer  *)
(*   nat).  Pure mathematical relation; NOT an algorithm mirror.     *)
(*                                                                   *)
(* pre_dfs2 is the phase-2 analogue over the forward graph; it also  *)
(* carries the SCC-id array sid_l.                                   *)
(* ================================================================= *)

(* ================================================================= *)
(* count_nonzero: number of nonzero entries in a Z list.             *)
(*   The C side encodes "visited" as 0/1 in vis1/vis2, so            *)
(*   count_nonzero vis_l = number of visited vertices.               *)
(*   The abstract DFS always visit1's a vertex BEFORE set_finish'ing *)
(*   it, hence timer <= count_nonzero vis, i.e. the difference       *)
(*   count_nonzero vis - timer = #visited-but-not-finished, which    *)
(*   dfs1 preserves.  This is the maintainable bound on the timer;   *)
(*   a bare `timer < n` is NOT maintainable through recursion.       *)
(* ================================================================= *)
Fixpoint count_nonzero (l : list Z) : Z :=
  match l with
  | nil => 0%Z
  | z :: rest => (if Z.eqb z 0 then 0%Z else 1%Z) + count_nonzero rest
  end.

Lemma count_nonzero_nonneg : forall (l : list Z), 0 <= count_nonzero l.
Proof. induction l as [| z l IH]; simpl; [lia | destruct (Z.eqb z 0); lia]. Qed.

Lemma count_nonzero_le_Zlength : forall (l : list Z), count_nonzero l <= Zlength l.
Proof.
  induction l as [| z l IH]; simpl.
  - rewrite Zlength_correct; simpl; lia.
  - rewrite Zlength_cons. destruct (Z.eqb z 0); lia.
Qed.

(* Replacing position u with a nonzero value v increases count_nonzero by
   exactly 1 iff the old entry at u was zero; otherwise it is unchanged.
   Requires u to be in range [0, Zlength l). *)
Lemma count_nonzero_replace_Znth :
  forall (u : Z) (v : Z) (l : list Z),
    (0 <= u < Zlength l)%Z ->
    count_nonzero (replace_Znth u v l) =
    count_nonzero l +
    (if Z.eqb (Znth u l 0) 0 then (if Z.eqb v 0 then 0%Z else 1%Z)
                              else (if Z.eqb v 0 then (-1)%Z else 0%Z)).
Proof.
  intros u v l. revert u.
  induction l as [| z l IH]; intros u Hin.
  - exfalso. rewrite Zlength_correct in Hin. simpl in Hin. lia.
  - simpl in Hin. destruct (Z.eqb u 0) eqn:HeqU.
    + (* u = 0: head z gets replaced by v *)
      apply Z.eqb_eq in HeqU. subst u.
      assert (Hz0 : Znth 0 (z :: l) 0 = z) by (rewrite Znth0_cons; reflexivity).
      rewrite Hz0.
      unfold replace_Znth. rewrite Z2Nat.inj_0. simpl.
      simpl count_nonzero at 2.
      destruct (Z.eqb z 0); destruct (Z.eqb v 0); lia.
    + (* u > 0: head z unchanged, recurse on tail with u-1 *)
      assert (Hpos : (0 < u)%Z) by (apply Z.eqb_neq in HeqU; lia).
      rewrite replace_Znth_cons by lia.
      simpl count_nonzero.
      rewrite Zlength_cons in Hin.
      assert (Hu1 : (0 <= u - 1 < Zlength l)%Z) by lia.
      rewrite IH by exact Hu1.
      assert (Heq : Znth u (z :: l) 0 = Znth (u - 1) l 0).
      { rewrite Znth_cons by lia. lia. }
      rewrite Heq.
      destruct (Z.eqb z 0); destruct (Z.eqb (Znth (u - 1) l 0) 0);
      destruct (Z.eqb v 0); lia.
Qed.

(* Specialisation: replacing a zero entry by 1 increases count by 1. *)
Lemma count_nonzero_replace_Znth01 :
  forall (u : Z) (l : list Z),
    (0 <= u < Zlength l)%Z ->
    Znth u l 0 = 0%Z ->
    count_nonzero (replace_Znth u 1 l) = count_nonzero l + 1.
Proof.
  intros u l Hin H. rewrite count_nonzero_replace_Znth by exact Hin.
  rewrite H. simpl. lia.
Qed.

(* Reading back a list after a positional write.  Generic, pure-list;       *)
(* used by the dfs2 Inv establishment/preservation (sid/vis after the       *)
(* preamble's vis[u]=1; sid[u]=sid[root], and the recurse-call poststate).  *)
Lemma Znth_replace_eq :
  forall (l: list Z) n (a d: Z),
    0 <= n < Zlength l ->
    Znth n (replace_Znth n a l) d = a.
Proof.
  intros l n a d Hn.
  unfold Znth, replace_Znth.
  rewrite Zlength_correct in Hn.
  remember (Z.to_nat n) as m eqn:Hm.
  assert (HmLen : (m < length l)%nat) by lia.
  clear Hn Hm n.
  revert l HmLen.
  induction m; intros l HmLen.
  - destruct l; simpl in *.
    + lia.
    + reflexivity.
  - destruct l; simpl in *.
    + lia.
    + apply IHm. lia.
Qed.

Lemma Znth_replace_neq :
  forall (l: list Z) i j (a d: Z),
    0 <= i < Zlength l ->
    0 <= j ->
    i <> j ->
    Znth i (replace_Znth j a l) d = Znth i l d.
Proof.
  intros l i j a d Hi Hj Hneq.
  unfold Znth, replace_Znth.
  rewrite Zlength_correct in Hi.
  remember (Z.to_nat i) as ni eqn:HiNat.
  remember (Z.to_nat j) as nj eqn:HjNat.
  assert (HiEq : i = Z.of_nat ni) by (subst; symmetry; apply Z2Nat.id; lia).
  assert (HjEq : j = Z.of_nat nj) by (subst; symmetry; apply Z2Nat.id; lia).
  assert (HiLen : (ni < length l)%nat) by lia.
  assert (HneqNat : ni <> nj).
  { intro Heq. apply Hneq. rewrite HiEq, HjEq. now rewrite Heq. }
  clear Hi Hj Hneq HiNat HjNat HiEq HjEq i j.
  revert nj l HiLen HneqNat.
  induction ni; intros nj l HiLen HneqNat.
  - destruct l; simpl in *; try lia.
    destruct nj; [contradiction HneqNat; reflexivity | reflexivity].
  - destruct l; simpl in *; try lia.
    destruct nj; simpl.
    + reflexivity.
    + apply IHni.
      * lia.
      * intro Heq. apply HneqNat. now f_equal.
Qed.

(* Pure C-side well-formedness of the CSR/graph input (no monad state).
   These describe the input arrays and the abstract graph; they belong in
   the C function's Require, NOT inside the safeExec precondition. *)
Definition csr_wf1 (g : AdjGraph)
  (radj_col_l radj_row_l vis1_l fin_l : list Z) : Prop :=
  AdjGraphValid g /\
  Zlength radj_row_l = adj_verts g + 1 /\
  Zlength vis1_l = adj_verts g /\
  Zlength fin_l = adj_verts g /\
  m_of radj_row_l = Zlength radj_col_l /\
  (forall u, (0 <= u < adj_verts g)%Z ->
     0 <= csr_lo u radj_row_l)%Z /\
  (forall u, (0 <= u < adj_verts g)%Z ->
     csr_hi u radj_row_l <= m_of radj_row_l)%Z /\
  (* every packed neighbour entry is a valid vertex id in [0, adj_verts g) *)
  (forall j, (0 <= j < m_of radj_row_l)%Z ->
     (0 <= Znth j radj_col_l 0 < adj_verts g)%Z) /\
  (* CSR row array is non-decreasing: each vertex's neighbour range is valid *)
  (forall u, (0 <= u < adj_verts g)%Z ->
     (csr_lo u radj_row_l <= csr_hi u radj_row_l)%Z) /\
  (m_of radj_row_l <= 2147483646)%Z.

Definition radj_col_particular (g: AdjGraph) (radj_col_l: list Z) : Prop :=
  forall j, (0 <= j < Zlength radj_col_l)%Z ->
     (0 <= Znth j radj_col_l 0 < adj_verts g)%Z.

(* CSR faithfulness: the packed CSR neighbour arrays list exactly the       *)
(* abstract graph's out-/in-neighbours.  This is the refinement link        *)
(* between the C cursor (a CSR position sweep) and the abstract monad's     *)
(* `step_aux g e u v` nondeterministic choice.  It is a pure mathematical   *)
(* property of the (immutable) graph + CSR arrays, so it is loop-invariant  *)
(* in the C code and cheap to carry through dfs1/dfs2.                      *)
Definition csr2_faithful (g: AdjGraph) (fadj_col_l fadj_row_l: list Z) : Prop :=
  forall u v, (0 <= u < adj_verts g)%Z -> (0 <= v < adj_verts g)%Z ->
    step g u v <->
    exists j, (csr_lo u fadj_row_l <= j < csr_hi u fadj_row_l)%Z /\ Znth j fadj_col_l 0 = v.

Definition csr1_faithful (g: AdjGraph) (radj_col_l radj_row_l: list Z) : Prop :=
  forall u v, (0 <= u < adj_verts g)%Z -> (0 <= v < adj_verts g)%Z ->
    step g v u <->
    exists j, (csr_lo u radj_row_l <= j < csr_hi u radj_row_l)%Z /\ Znth j radj_col_l 0 = v.

(* pre_dfs1: ONLY the C-program-state <-> monad-state correspondence. *)
Definition pre_dfs1 (g : AdjGraph)
  (radj_col_l radj_row_l vis1_l fin_l : list Z) (timer_v : Z)
  (st : KSt) : Prop :=
  (forall u, (0 <= u < adj_verts g)%Z ->
     visited1 st u <-> Znth u vis1_l 0 <> 0%Z) /\
  (forall u, (0 <= u < adj_verts g)%Z ->
     finish st u = Z.to_nat (Znth u fin_l 0)) /\
  timer st = Z.to_nat timer_v.

Definition csr_wf2 (g : AdjGraph)
  (fadj_col_l fadj_row_l vis2_l sid_l : list Z) : Prop :=
  AdjGraphValid g /\
  Zlength fadj_row_l = adj_verts g + 1 /\
  Zlength vis2_l = adj_verts g /\
  Zlength sid_l = adj_verts g /\
  m_of fadj_row_l = Zlength fadj_col_l /\
  (forall u, (0 <= u < adj_verts g)%Z ->
     0 <= csr_lo u fadj_row_l)%Z /\
  (forall u, (0 <= u < adj_verts g)%Z ->
     csr_hi u fadj_row_l <= m_of fadj_row_l)%Z /\
  (* every packed neighbour entry is a valid vertex id in [0, adj_verts g) *)
  (forall j, (0 <= j < m_of fadj_row_l)%Z ->
     (0 <= Znth j fadj_col_l 0 < adj_verts g)%Z) /\
  (* CSR row array is non-decreasing: each vertex's neighbour range is valid *)
  (forall u, (0 <= u < adj_verts g)%Z ->
     (csr_lo u fadj_row_l <= csr_hi u fadj_row_l)%Z) /\
  (m_of fadj_row_l <= 2147483646)%Z.

(* pre_dfs2: ONLY the C-program-state <-> monad-state correspondence. *)
Definition pre_dfs2 (g : AdjGraph)
  (fadj_col_l fadj_row_l vis2_l sid_l : list Z) (root_v : Z)
  (st : KSt) : Prop :=
  (forall u, (0 <= u < adj_verts g)%Z ->
     visited2 st u <-> Znth u vis2_l 0 <> 0%Z) /\
  (forall u, (0 <= u < adj_verts g)%Z ->
     scc_id st u = Z.to_nat (Znth u sid_l 0)).

(* ================================================================= *)
(* Loop continuations — cursor-parameterised.                        *)
(*                                                                   *)
(* The abstract DFS_finish u / DFS_scc root u are non-deterministic  *)
(* over (e,v) ∈ E×V.  The C side reifies this choice as a CSR cursor  *)
(* sweep over u's reverse (resp. forward) neighbours: at cursor i    *)
(* the chosen vertex is radj_col_l[i] (resp. fadj_col_l[i]).         *)
(*                                                                   *)
(* dfs_finish_iter g radj_col_l u i n is a structurally decreasing   *)
(* (fuel n) cursor sweep starting at i: at each step it descends     *)
(* into dfs_finish g (radj_col_l[i]) and continues at i+1; once the  *)
(* cursor reaches hi (i.e. n fuel exhausted / i >= hi) it re-enters  *)
(* dfs_finish g u, which — with all reverse neighbours now visited — *)
(* performs only the set_finish u timer tail of the abstract DFS.    *)
(*                                                                   *)
(* dfs_finish_from g radj_col_l radj_row_l u i is the cursor-resumed *)
(* continuation with fuel (hi - i), where hi = csr_hi u radj_row_l.  *)
(*                                                                   *)
(* This is NOT a mirror of the C algorithm: it is an abstract-monad  *)
(* program whose four structural unfoldings (entry / step-rec /      *)
(* step-skip / exit) discharge by Fixpoint computation.  No Admitted, *)
(* Axiom or Parameter is used here; the VCs these induce are the     *)
(* manual obligations for the proving phase.                         *)
(* ================================================================= *)

Fixpoint dfs_finish_iter
  (g : AdjGraph) (radj_col_l : list Z) (u hi i : Z) (fuel : nat)
  : program KSt unit :=
  match fuel with
  | O => dfs_finish g u
  | S fuel' =>
      if Z.leb hi i then dfs_finish g u
      else (_ <- dfs_finish g (Znth i radj_col_l 0) ;;
             dfs_finish_iter g radj_col_l u hi (i + 1) fuel')
  end.

Fixpoint dfs_scc_iter
  (g : AdjGraph) (fadj_col_l : list Z) (root u hi i : Z) (fuel : nat)
  : program KSt unit :=
  match fuel with
  | O => dfs_scc g root u
  | S fuel' =>
      if Z.leb hi i then dfs_scc g root u
      else
        (* B1: vis-conditional cursor — matches the C `if (vis2[v]==0)` and the
           abstract repeat_break's `assume ~visited2 st v` guard.  At position
           i, v = Znth i fadj_col_l 0: if v is already visited2, SKIP (advance
           cursor); otherwise RECURSE into dfs_scc root v then advance. *)
        if_else (fun st => visited2 st (Znth i fadj_col_l 0))
                (dfs_scc_iter g fadj_col_l root u hi (i + 1) fuel')
                (_ <- dfs_scc g root (Znth i fadj_col_l 0) ;;
                 dfs_scc_iter g fadj_col_l root u hi (i + 1) fuel')
  end.

Definition dfs_finish_from
  (g : AdjGraph) (radj_col_l radj_row_l : list Z) (u i : Z) : program KSt unit :=
  dfs_finish_iter g radj_col_l u (csr_hi u radj_row_l) i
    (Z.to_nat (csr_hi u radj_row_l - i)).

Definition dfs_scc_from
  (g : AdjGraph) (fadj_col_l fadj_row_l : list Z) (root u i : Z) : program KSt unit :=
  dfs_scc_iter g fadj_col_l root u (csr_hi u fadj_row_l) i
    (Z.to_nat (csr_hi u fadj_row_l - i)).

Definition dfs_finish_fromK
  (g : AdjGraph) (radj_col_l radj_row_l : list Z) (u i : Z) : unit -> program KSt unit :=
  fun _ => dfs_finish_from g radj_col_l radj_row_l u i.

Definition dfs_scc_fromK
  (g : AdjGraph) (fadj_col_l fadj_row_l : list Z) (root u i : Z) : unit -> program KSt unit :=
  fun _ => dfs_scc_from g fadj_col_l fadj_row_l root u i.

(* ================================================================= *)
(* Structural unfolding lemmas for the cursor continuations.          *)
(*                                                                   *)
(* These discharge by Fixpoint computation; they expose the cursor    *)
(* step (recurse into the chosen neighbour, continue at i+1) and the  *)
(* exit (cursor exhausted: re-enter dfs_finish / dfs_scc to run the   *)
(* abstract set_finish / finalisation tail).  No Admitted / Axiom.    *)
(* ================================================================= *)

Lemma dfs_finish_iter_step :
  forall (g : AdjGraph) (radj_col_l : list Z) (u hi i : Z) (fuel : nat),
    (i < hi)%Z ->
    dfs_finish_iter g radj_col_l u hi i (S fuel)
    == (_ <- dfs_finish g (Znth i radj_col_l 0) ;;
        dfs_finish_iter g radj_col_l u hi (i + 1) fuel).
Proof.
  intros g radj_col_l u hi i fuel Hilt.
  simpl.
  destruct (Z.leb hi i) eqn:E.
  - apply Z.leb_le in E. lia.
  - reflexivity.
Qed.

Lemma dfs_finish_iter_exit :
  forall (g : AdjGraph) (radj_col_l : list Z) (u hi i : Z) (fuel : nat),
    (hi <= i)%Z ->
    dfs_finish_iter g radj_col_l u hi i (S fuel) == dfs_finish g u.
Proof.
  intros g radj_col_l u hi i fuel Hge.
  simpl.
  destruct (Z.leb hi i) eqn:E.
  - reflexivity.
  - apply Z.leb_nle in E. lia.
Qed.

Lemma dfs_scc_iter_skip_step :
  forall (g : AdjGraph) (fadj_col_l : list Z) (root u hi i : Z) (fuel : nat)
         (st : KSt) (a : unit) (s' : KSt),
    (i < hi)%Z ->
    visited2 st (Znth i fadj_col_l 0) ->
    (dfs_scc_iter g fadj_col_l root u hi i (S fuel)).(MonadErr.nrm) st a s' <->
    (dfs_scc_iter g fadj_col_l root u hi (i + 1) fuel).(MonadErr.nrm) st a s'.
Proof.
  intros g fadj_col_l root u hi i fuel st a s' Hilt Hvis.
  simpl. destruct (Z.leb hi i) eqn:E.
  - apply Z.leb_le in E. exfalso. lia.
  - unfold if_else, choice, test. unfold_monad. sets_unfold.
    split.
    + intros [H | H].
      * destruct H as [b [s2 [[Hs2 Hcond] Hsk]]]. subst s2. exact Hsk.
      * destruct H as [b [s2 [[Hs2 Hncond] _]]]. exfalso. apply Hncond. exact Hvis.
    + intros Hsk. left. exists tt. exists st. split; [ split; [ reflexivity | exact Hvis ] | exact Hsk ].
Qed.

Lemma dfs_scc_iter_recurse_step :
  forall (g : AdjGraph) (fadj_col_l : list Z) (root u hi i : Z) (fuel : nat)
         (st : KSt) (a : unit) (s' : KSt),
    (i < hi)%Z ->
    ~ visited2 st (Znth i fadj_col_l 0) ->
    (dfs_scc_iter g fadj_col_l root u hi i (S fuel)).(MonadErr.nrm) st a s' <->
    ((_ <- dfs_scc g root (Znth i fadj_col_l 0) ;;
      dfs_scc_iter g fadj_col_l root u hi (i + 1) fuel)).(MonadErr.nrm) st a s'.
Proof.
  intros g fadj_col_l root u hi i fuel st a s' Hilt Hnvis.
  simpl. destruct (Z.leb hi i) eqn:E.
  - apply Z.leb_le in E. exfalso. lia.
  - unfold if_else, choice, test. unfold_monad. sets_unfold.
    split.
    + intros [H | H].
      * destruct H as [b [s2 [[Hs2 Hcond] _]]]. exfalso. apply Hnvis. exact Hcond.
      * destruct H as [b [s2 [[Hs2 Hncond] Hrec]]]. subst s2. exact Hrec.
    + intros Hrec. right. exists tt. exists st. split; [ split; [ reflexivity | exact Hnvis ] | exact Hrec ].
Qed.

Lemma dfs_scc_iter_exit :
  forall (g : AdjGraph) (fadj_col_l : list Z) (root u hi i : Z) (fuel : nat),
    (hi <= i)%Z ->
    dfs_scc_iter g fadj_col_l root u hi i (S fuel) == dfs_scc g root u.
Proof.
  intros g fadj_col_l root u hi i fuel Hge.
  simpl.
  destruct (Z.leb hi i) eqn:E.
  - reflexivity.
  - apply Z.leb_nle in E. lia.
Qed.

(* Under MonadErr, `program Σ A` is a record {nrm; err}.  dfs_scc (hence
   dfs_scc_iter / dfs_scc_from, which are built only from dfs_scc, if_else,
   choice, test, and bind) never raises an error: every construct used has an
   empty err component (dfs_scc_f's body uses assume, not assert/assertS; the
   custom visit2/set_scc_id have err := ∅).  We never need to prove the
   full no-error fact by induction over BW_fix iterations, because the
   safeExec-based skip/recurse closers only need an err IMPLICATION
   (err-at-i+1 -> err-at-i) under the visited/¬visited cursor hypothesis,
   which follows by one-level unfolding of the if_else/choice/bind err
   structure (using bind_err_iff / bind_nrm_iff from MonadErrBasic). *)
Lemma dfs_scc_iter_skip_err_imp :
  forall (g : AdjGraph) (fadj_col_l : list Z) (root u hi i : Z) (fuel : nat)
         (st : KSt),
    (i < hi)%Z ->
    visited2 st (Znth i fadj_col_l 0) ->
    (dfs_scc_iter g fadj_col_l root u hi (i + 1) fuel).(MonadErr.err) st ->
    (dfs_scc_iter g fadj_col_l root u hi i (S fuel)).(MonadErr.err) st.
Proof.
  intros g fadj_col_l root u hi i fuel st Hilt Hvis Herr.
  simpl. destruct (Z.leb hi i) eqn:E.
  - apply Z.leb_le in E. exfalso. lia.
  - unfold if_else, choice. sets_unfold.
    left. rewrite bind_err_iff. right.
    exists tt. exists st. split; [ | exact Herr ].
    unfold test. sets_unfold. split; [ reflexivity | exact Hvis ].
Qed.

Lemma dfs_scc_iter_recurse_err_imp :
  forall (g : AdjGraph) (fadj_col_l : list Z) (root u hi i : Z) (fuel : nat)
         (st : KSt),
    (i < hi)%Z ->
    ~ visited2 st (Znth i fadj_col_l 0) ->
    ((_ <- dfs_scc g root (Znth i fadj_col_l 0) ;;
      dfs_scc_iter g fadj_col_l root u hi (i + 1) fuel)).(MonadErr.err) st ->
    (dfs_scc_iter g fadj_col_l root u hi i (S fuel)).(MonadErr.err) st.
Proof.
  intros g fadj_col_l root u hi i fuel st Hilt Hnvis Herr.
  simpl. destruct (Z.leb hi i) eqn:E.
  - apply Z.leb_le in E. exfalso. lia.
  - unfold if_else, choice. sets_unfold.
    right. rewrite bind_err_iff. right.
    exists tt. exists st. split; [ | exact Herr ].
    unfold test. sets_unfold. split; [ reflexivity | exact Hnvis ].
Qed.

(* The dfs_finish_from / dfs_scc_from level lemmas, accounting for the
   Z.to_nat fuel accounting.  When i < hi, Z.to_nat (hi - i) = S _ and
   the next cursor's fuel is Z.to_nat (hi - (i+1)) = pred (Z.to_nat (hi-i)). *)

Lemma dfs_finish_from_step :
  forall (g : AdjGraph) (radj_col_l radj_row_l : list Z) (u i : Z),
    (i < csr_hi u radj_row_l)%Z ->
    dfs_finish_from g radj_col_l radj_row_l u i
    == (_ <- dfs_finish g (Znth i radj_col_l 0) ;;
        dfs_finish_from g radj_col_l radj_row_l u (i + 1)).
Proof.
  intros g radj_col_l radj_row_l u i Hilt.
  unfold dfs_finish_from.
  assert (Hfuel : Z.to_nat (csr_hi u radj_row_l - i) =
                  S (Z.to_nat (csr_hi u radj_row_l - (i + 1)))).
  { assert (Hsub : csr_hi u radj_row_l - i =
                   (csr_hi u radj_row_l - (i + 1)) + 1) by lia.
    rewrite Hsub, Z2Nat.inj_add by lia.
    rewrite Nat.add_1_r. reflexivity. }
  rewrite Hfuel.
  apply dfs_finish_iter_step. lia.
Qed.

Lemma dfs_finish_from_exit :
  forall (g : AdjGraph) (radj_col_l radj_row_l : list Z) (u i : Z),
    (csr_hi u radj_row_l <= i)%Z ->
    dfs_finish_from g radj_col_l radj_row_l u i == dfs_finish g u.
Proof.
  intros g radj_col_l radj_row_l u i Hge.
  unfold dfs_finish_from.
  destruct (Z.to_nat (csr_hi u radj_row_l - i)) eqn:E.
  - reflexivity.
  - apply dfs_finish_iter_exit. exact Hge.
Qed.

Lemma dfs_scc_from_skip_step :
  forall (g : AdjGraph) (fadj_col_l fadj_row_l : list Z) (root u i : Z)
         (st : KSt) (a : unit) (s' : KSt),
    (i < csr_hi u fadj_row_l)%Z ->
    visited2 st (Znth i fadj_col_l 0) ->
    (dfs_scc_from g fadj_col_l fadj_row_l root u i).(MonadErr.nrm) st a s' <->
    (dfs_scc_from g fadj_col_l fadj_row_l root u (i + 1)).(MonadErr.nrm) st a s'.
Proof.
  intros g fadj_col_l fadj_row_l root u i st a s' Hilt Hvis.
  unfold dfs_scc_from.
  assert (Hfuel : Z.to_nat (csr_hi u fadj_row_l - i) =
                  S (Z.to_nat (csr_hi u fadj_row_l - (i + 1)))).
  { assert (Hsub : csr_hi u fadj_row_l - i =
                   (csr_hi u fadj_row_l - (i + 1)) + 1) by lia.
    rewrite Hsub, Z2Nat.inj_add by lia.
    rewrite Nat.add_1_r. reflexivity. }
  rewrite Hfuel. apply dfs_scc_iter_skip_step; [ lia | exact Hvis ].
Qed.

Lemma dfs_scc_from_recurse_step :
  forall (g : AdjGraph) (fadj_col_l fadj_row_l : list Z) (root u i : Z)
         (st : KSt) (a : unit) (s' : KSt),
    (i < csr_hi u fadj_row_l)%Z ->
    ~ visited2 st (Znth i fadj_col_l 0) ->
    (dfs_scc_from g fadj_col_l fadj_row_l root u i).(MonadErr.nrm) st a s' <->
    ((_ <- dfs_scc g root (Znth i fadj_col_l 0) ;;
      dfs_scc_from g fadj_col_l fadj_row_l root u (i + 1))).(MonadErr.nrm) st a s'.
Proof.
  intros g fadj_col_l fadj_row_l root u i st a s' Hilt Hnvis.
  unfold dfs_scc_from.
  assert (Hfuel : Z.to_nat (csr_hi u fadj_row_l - i) =
                  S (Z.to_nat (csr_hi u fadj_row_l - (i + 1)))).
  { assert (Hsub : csr_hi u fadj_row_l - i =
                   (csr_hi u fadj_row_l - (i + 1)) + 1) by lia.
    rewrite Hsub, Z2Nat.inj_add by lia.
    rewrite Nat.add_1_r. reflexivity. }
  rewrite Hfuel. apply dfs_scc_iter_recurse_step; [ lia | exact Hnvis ].
Qed.

Lemma dfs_scc_from_skip_err_imp :
  forall (g : AdjGraph) (fadj_col_l fadj_row_l : list Z) (root u i : Z)
         (st : KSt),
    (i < csr_hi u fadj_row_l)%Z ->
    visited2 st (Znth i fadj_col_l 0) ->
    (dfs_scc_from g fadj_col_l fadj_row_l root u (i + 1)).(MonadErr.err) st ->
    (dfs_scc_from g fadj_col_l fadj_row_l root u i).(MonadErr.err) st.
Proof.
  intros g fadj_col_l fadj_row_l root u i st Hilt Hvis Herr.
  unfold dfs_scc_from in *.
  assert (Hfuel : Z.to_nat (csr_hi u fadj_row_l - i) =
                  S (Z.to_nat (csr_hi u fadj_row_l - (i + 1)))).
  { assert (Hsub : csr_hi u fadj_row_l - i =
                   (csr_hi u fadj_row_l - (i + 1)) + 1) by lia.
    rewrite Hsub, Z2Nat.inj_add by lia.
    rewrite Nat.add_1_r. reflexivity. }
  rewrite Hfuel. apply dfs_scc_iter_skip_err_imp; [ exact Hilt | exact Hvis | exact Herr ].
Qed.

Lemma dfs_scc_from_recurse_err_imp :
  forall (g : AdjGraph) (fadj_col_l fadj_row_l : list Z) (root u i : Z)
         (st : KSt),
    (i < csr_hi u fadj_row_l)%Z ->
    ~ visited2 st (Znth i fadj_col_l 0) ->
    ((_ <- dfs_scc g root (Znth i fadj_col_l 0) ;;
      dfs_scc_from g fadj_col_l fadj_row_l root u (i + 1))).(MonadErr.err) st ->
    (dfs_scc_from g fadj_col_l fadj_row_l root u i).(MonadErr.err) st.
Proof.
  intros g fadj_col_l fadj_row_l root u i st Hilt Hnvis Herr.
  unfold dfs_scc_from in *.
  assert (Hfuel : Z.to_nat (csr_hi u fadj_row_l - i) =
                  S (Z.to_nat (csr_hi u fadj_row_l - (i + 1)))).
  { assert (Hsub : csr_hi u fadj_row_l - i =
                   (csr_hi u fadj_row_l - (i + 1)) + 1) by lia.
    rewrite Hsub, Z2Nat.inj_add by lia.
    rewrite Nat.add_1_r. reflexivity. }
  rewrite Hfuel. apply dfs_scc_iter_recurse_err_imp; [ exact Hilt | exact Hnvis | exact Herr ].
Qed.

Lemma dfs_scc_from_exit :
  forall (g : AdjGraph) (fadj_col_l fadj_row_l : list Z) (root u i : Z),
    (csr_hi u fadj_row_l <= i)%Z ->
    dfs_scc_from g fadj_col_l fadj_row_l root u i == dfs_scc g root u.
Proof.
  intros g fadj_col_l fadj_row_l root u i Hge.
  unfold dfs_scc_from.
  destruct (Z.to_nat (csr_hi u fadj_row_l - i)) eqn:E.
  - reflexivity.
  - apply dfs_scc_iter_exit. exact Hge.
Qed.

(* dfs2_return_close (the Gap-A loop-exit closer) was HERE; it depended on   *)
(* the absorb chain (dfs_scc_safe_return) and is deleted alongside it — see   *)
(* the SEMANTIC GAP note near the former dfs_scc_absorb.                       *)


(* B1 fallouts: conditional step-closers for the recurse VC (partial_solve_8)
   and the Gap-B skip VC.  Each extracts the safeExec witness sigma, derives
   visited2/~visited2 of v (= Znth i fadj_col_l 0) at sigma via pre_dfs2, applies
   dfs_scc_from_skip_step / dfs_scc_from_recurse_step, and reconstructs. *)
Lemma dfs2_skip_close :
  forall (g: AdjGraph) (fadj_col_l fadj_row_l: list Z) (root u i: Z)
         (vis2_m sid_m: list Z) (root_v: Z) (X: unit -> KSt -> Prop),
  (i < csr_hi u fadj_row_l)%Z ->
  (0 <= Znth i fadj_col_l 0 < adj_verts g)%Z ->
  Znth (Znth i fadj_col_l 0) vis2_m 0 <> 0%Z ->
  safeExec (pre_dfs2 g fadj_col_l fadj_row_l vis2_m sid_m root_v)
           (dfs_scc_from g fadj_col_l fadj_row_l root u i) X ->
  safeExec (pre_dfs2 g fadj_col_l fadj_row_l vis2_m sid_m root_v)
           (dfs_scc_from g fadj_col_l fadj_row_l root u (i + 1)) X.
Proof.
  intros g fadj_col_l fadj_row_l root u i vis2_m sid_m root_v X
         Hilt Hvvb Hvvis Hsccfrom.
  destruct Hsccfrom as [sigma [Hpre Hsafe]].
  destruct Hpre as [Hpv Hps].
  assert (Hvisv : visited2 sigma (Znth i fadj_col_l 0))
    by (exact (proj2 (Hpv (Znth i fadj_col_l 0) Hvvb) Hvvis)).
  unfold safeExec. exists sigma. split.
  - unfold pre_dfs2; split; assumption.
  - unfold safe, weakestpre. split.
    + intros Herr. destruct Hsafe as [Hnoerr _]. exfalso. apply Hnoerr.
      apply (dfs_scc_from_skip_err_imp g fadj_col_l fadj_row_l root u i sigma Hilt Hvisv).
      exact Herr.
    + intros a s' Ht. destruct Hsafe as [_ Hpost]. apply Hpost.
      apply (proj2 (dfs_scc_from_skip_step g fadj_col_l fadj_row_l root u i sigma a s' Hilt Hvisv)).
      exact Ht.
Qed.

Lemma dfs2_recurse_close :
  forall (g: AdjGraph) (fadj_col_l fadj_row_l: list Z) (root u i: Z)
         (vis2_m sid_m: list Z) (root_v: Z) (X: unit -> KSt -> Prop),
  (i < csr_hi u fadj_row_l)%Z ->
  (0 <= Znth i fadj_col_l 0 < adj_verts g)%Z ->
  Znth (Znth i fadj_col_l 0) vis2_m 0 = 0%Z ->
  safeExec (pre_dfs2 g fadj_col_l fadj_row_l vis2_m sid_m root_v)
           (dfs_scc_from g fadj_col_l fadj_row_l root u i) X ->
  safeExec (pre_dfs2 g fadj_col_l fadj_row_l vis2_m sid_m root_v)
           (bind (dfs_scc g root (Znth i fadj_col_l 0))
                 (dfs_scc_fromK g fadj_col_l fadj_row_l root u (i + 1))) X.
Proof.
  intros g fadj_col_l fadj_row_l root u i vis2_m sid_m root_v X
         Hilt Hvvb Hvvis0 Hsccfrom.
  destruct Hsccfrom as [sigma [Hpre Hsafe]].
  destruct Hpre as [Hpv Hps].
  assert (Hnvisv : ~ visited2 sigma (Znth i fadj_col_l 0)).
  { intro Hvv.
    assert (Hzz : Znth (Znth i fadj_col_l 0) vis2_m 0 <> 0%Z)
      by (apply (proj1 (Hpv (Znth i fadj_col_l 0) Hvvb)); exact Hvv).
    lia. }
  unfold safeExec. exists sigma. split.
  - unfold pre_dfs2; split; assumption.
  - unfold safe, weakestpre. split.
    + intros Herr. destruct Hsafe as [Hnoerr _]. exfalso. apply Hnoerr.
      apply (dfs_scc_from_recurse_err_imp g fadj_col_l fadj_row_l root u i sigma Hilt Hnvisv).
      exact Herr.
    + intros a s' Ht. destruct Hsafe as [_ Hpost]. apply Hpost.
      apply (proj2 (dfs_scc_from_recurse_step g fadj_col_l fadj_row_l root u i sigma a s' Hilt Hnvisv)).
      exact Ht.
Qed.

(* Scanned-neighbours conjunct helper (dfs2_entail_wit_3 group).  At cursor i,
   vertex v = Znth i fadj_col_l 0.  The conjunct requires both the lo-end
   neighbour and the i-end (= v) neighbour to be visited2.  The i-end is just
   v's visited fact (Hvisv); the lo-end is the scanned range [lo, i) when lo < i,
   or reduces to v when lo = i (the range is then empty and Znth lo = v).  This
   encapsulates the lo=i case split so the main-VC dispatch need not key on
   PreH numbers (reorder-immune). *)
Lemma dfs2_scanned_lo_close :
  forall (fc vis: list Z) (lo i v: Z),
    (forall j, ((lo <= j)%Z /\ (j < i)%Z) -> Znth (Znth j fc 0) vis 0 <> 0%Z) ->
    (lo <= i)%Z ->
    v = Znth i fc 0 ->
    Znth v vis 0 <> 0%Z ->
    Znth (Znth lo fc 0) vis 0 <> 0%Z.
Proof.
  intros fc vis lo i v Hscan Hli Hv Hvisv.
  destruct (Z.eqb lo i) eqn:E.
  - apply Z.eqb_eq in E. subst i. rewrite <- Hv. exact Hvisv.
  - apply Z.eqb_neq in E. assert (Hlli : ((lo <= lo)%Z /\ (lo < i)%Z)) by lia.
    exact (Hscan lo Hlli).
Qed.
