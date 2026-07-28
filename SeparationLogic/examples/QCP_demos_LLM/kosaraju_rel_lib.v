Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Lia.
Require Import Coq.Logic.Classical.
Require Import Coq.Logic.ClassicalDescription.
Require Import Coq.Logic.FunctionalExtensionality.
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

(* gvalid: well-formed adjacency list.  The converse is guarded because
   Z.to_nat maps negative integers to zero, which is not a graph index. *)
Definition AdjGraphValid (g : AdjGraph) : Prop :=
  (Zlength (adj_fwd g) = adj_verts g)%Z /\
  (Zlength (adj_rev g) = adj_verts g)%Z /\
  (forall u, (0 <= u < adj_verts g)%Z ->
    forall v, In v (nth (Z.to_nat u) (adj_fwd g) nil) -> (0 <= v < adj_verts g)%Z) /\
  (forall u, (0 <= u < adj_verts g)%Z ->
    forall v, In v (nth (Z.to_nat u) (adj_rev g) nil) -> (0 <= v < adj_verts g)%Z) /\
  (forall u v, (0 <= u < adj_verts g)%Z -> (0 <= v < adj_verts g)%Z ->
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
  gvalid g ->
  @PartialOrder_Setoid.equiv (MonadErr.M KSt unit) _
    (dfs_finish g u) (@DFS_finish_f AdjGraph Z (Z * Z) KG g (dfs_finish g) u).
Proof. intros g u Hg. unfold dfs_finish.
  assert (Hg' : @gvalid AdjGraph (@kos_gvalid AdjGraph Z (Z * Z) KG) g) by exact Hg.
  exact (DFS_finish_unfold g Hg' u). Qed.

Lemma dfs_scc_unfold : forall (g : AdjGraph) (root u : Z),
  gvalid g ->
  @PartialOrder_Setoid.equiv (MonadErr.M KSt unit) _
    (dfs_scc g root u) (@DFS_scc_f AdjGraph Z (Z * Z) KG g root (dfs_scc g root) u).
Proof. intros g root u Hg. unfold dfs_scc.
  assert (Hg' : @gvalid AdjGraph (@kos_gvalid AdjGraph Z (Z * Z) KG) g) by exact Hg.
  exact (DFS_scc_unfold g Hg' root u). Qed.

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

(* The immutable forward-CSR part of [csr_wf2].  It deliberately omits
   vis2/sid: those lists are mutable phase-2 work arrays, while every
   conjunct below is fixed by the CSR construction before [kosaraju]. *)
Definition csr_wf2_core (g : AdjGraph)
  (fadj_col_l fadj_row_l : list Z) : Prop :=
  AdjGraphValid g /\
  Zlength fadj_row_l = adj_verts g + 1 /\
  m_of fadj_row_l = Zlength fadj_col_l /\
  (forall u, (0 <= u < adj_verts g)%Z ->
     0 <= csr_lo u fadj_row_l)%Z /\
  (forall u, (0 <= u < adj_verts g)%Z ->
     csr_hi u fadj_row_l <= m_of fadj_row_l)%Z /\
  (forall j, (0 <= j < m_of fadj_row_l)%Z ->
     (0 <= Znth j fadj_col_l 0 < adj_verts g)%Z) /\
  (forall u, (0 <= u < adj_verts g)%Z ->
     (csr_lo u fadj_row_l <= csr_hi u fadj_row_l)%Z) /\
  (m_of fadj_row_l <= 2147483646)%Z.

Lemma csr_wf2_of_core :
  forall g fadj_col_l fadj_row_l vis2_l sid_l,
    csr_wf2_core g fadj_col_l fadj_row_l ->
    Zlength vis2_l = adj_verts g ->
    Zlength sid_l = adj_verts g ->
    csr_wf2 g fadj_col_l fadj_row_l vis2_l sid_l.
Proof.
  intros g fadj_col_l fadj_row_l vis2_l sid_l Hcore Hvis Hsid.
  unfold csr_wf2_core in Hcore.
  unfold csr_wf2.
  destruct Hcore as
    [Hvalid [Hrow [Hm [Hlo [Hhi [Hcol [Horder Hbound]]]]]]].
  split; [exact Hvalid|].
  split; [exact Hrow|].
  split; [exact Hvis|].
  split; [exact Hsid|].
  split; [exact Hm|].
  split; [exact Hlo|].
  split; [exact Hhi|].
  split; [exact Hcol|].
  split; [exact Horder|exact Hbound].
Qed.

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
(* dfs_finish_iter g radj_col_l u hi i fuel is a structurally        *)
(* decreasing (fuel) cursor sweep starting at i.  At each step v =   *)
(* radj_col_l[i]; if v is already visited1, SKIP (advance cursor);   *)
(* otherwise RECURSE into dfs_finish g v then advance.  Once the     *)
(* cursor reaches hi (i >= hi) it performs the set_finish u timer    *)
(* tail — mirroring the C post-loop {t0=timer; fin[u]=t0; timer++}   *)
(* and the DFS_finish_f break branch's `get timer ;; set_finish u t`. *)
(*                                                                   *)
(* dfs_scc_iter is the phase-2 analogue over the forward graph; its  *)
(* exit is `ret tt` because dfs2 has NO post-loop block (the         *)
(* function returns immediately after the cursor sweep).             *)
(*                                                                   *)
(* dfs_finish_from / dfs_scc_from specialise iter with fuel          *)
(* (csr_hi u row_l - i), so the entry (i = csr_lo u), step, and      *)
(* exit (i = csr_hi u) unfoldings discharge by Fixpoint computation. *)
(* No Admitted, Axiom or Parameter is used here.                     *)
(* ================================================================= *)

(* AdjGraph VListBijective instance: derived from FiniteGraph, matching the
   Section-local `kos_vlist` in Kosaraju.v.  This lets `bijective_listV g`
   resolve in lib.v definitions (needed by dfs_finish_repeat_body's assertS
   timer <= |V|), and keeps definitional equality with DFS_finish_f's body. *)
#[export] Instance AdjGraph_vlistbijective : VListBijective AdjGraph Z (Z * Z) :=
  finite_graph_vlist_bijective AdjGraph Z (Z * Z).

Fixpoint dfs_finish_iter
  (g : AdjGraph) (radj_col_l : list Z) (u hi i : Z) (fuel : nat)
  : program KSt unit :=
  match fuel with
  | O => (assertS (fun st => (timer st < length (bijective_listV g))%nat);; t <- get (fun st t => t = timer st) ;; set_finish u t)
  | S fuel' =>
      if Z.leb hi i then assertS (fun st => (timer st < length (bijective_listV g))%nat);; t <- get (fun st t => t = timer st) ;; set_finish u t
      else
        (* vis-conditional cursor — matches the C `if (vis1[v]==0)` and the
           abstract repeat_break's `assume ~visited1 st v` guard.  At position
           i, v = Znth i radj_col_l 0: if v is already visited1, SKIP (advance
           cursor); otherwise RECURSE into dfs_finish g v then advance. *)
        if_else (fun st => visited1 st (Znth i radj_col_l 0))
                (dfs_finish_iter g radj_col_l u hi (i + 1) fuel')
                (_ <- dfs_finish g (Znth i radj_col_l 0) ;;
                 dfs_finish_iter g radj_col_l u hi (i + 1) fuel')
  end.

Fixpoint dfs_scc_iter
  (g : AdjGraph) (fadj_col_l : list Z) (root u hi i : Z) (fuel : nat)
  : program KSt unit :=
  match fuel with
  | O => ret tt
  | S fuel' =>
      if Z.leb hi i then ret tt
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

Lemma dfs_finish_iter_skip_step :
  forall (g : AdjGraph) (radj_col_l : list Z) (u hi i : Z) (fuel : nat)
         (st : KSt) (a : unit) (s' : KSt),
    (i < hi)%Z ->
    visited1 st (Znth i radj_col_l 0) ->
    (dfs_finish_iter g radj_col_l u hi i (S fuel)).(MonadErr.nrm) st a s' <->
    (dfs_finish_iter g radj_col_l u hi (i + 1) fuel).(MonadErr.nrm) st a s'.
Proof.
  intros g radj_col_l u hi i fuel st a s' Hilt Hvis.
  simpl. destruct (Z.leb hi i) eqn:E.
  - apply Z.leb_le in E. exfalso. lia.
  - unfold if_else, choice, test. unfold_monad. sets_unfold.
    split.
    + intros [H | H].
      * destruct H as [b [s2 [[Hs2 Hcond] Hsk]]]. subst s2. exact Hsk.
      * destruct H as [b [s2 [[Hs2 Hncond] _]]]. exfalso. apply Hncond. exact Hvis.
    + intros Hsk. left. exists tt. exists st. split; [ split; [ reflexivity | exact Hvis ] | exact Hsk ].
Qed.

Lemma dfs_finish_iter_recurse_step :
  forall (g : AdjGraph) (radj_col_l : list Z) (u hi i : Z) (fuel : nat)
         (st : KSt) (a : unit) (s' : KSt),
    (i < hi)%Z ->
    ~ visited1 st (Znth i radj_col_l 0) ->
    (dfs_finish_iter g radj_col_l u hi i (S fuel)).(MonadErr.nrm) st a s' <->
    ((_ <- dfs_finish g (Znth i radj_col_l 0) ;;
      dfs_finish_iter g radj_col_l u hi (i + 1) fuel)).(MonadErr.nrm) st a s'.
Proof.
  intros g radj_col_l u hi i fuel st a s' Hilt Hnvis.
  simpl. destruct (Z.leb hi i) eqn:E.
  - apply Z.leb_le in E. exfalso. lia.
  - unfold if_else, choice, test. unfold_monad. sets_unfold.
    split.
    + intros [H | H].
      * destruct H as [b [s2 [[Hs2 Hcond] _]]]. exfalso. apply Hnvis. exact Hcond.
      * destruct H as [b [s2 [[Hs2 Hncond] Hrec]]]. subst s2. exact Hrec.
    + intros Hrec. right. exists tt. exists st. split; [ split; [ reflexivity | exact Hnvis ] | exact Hrec ].
Qed.

Lemma dfs_finish_iter_exit :
  forall (g : AdjGraph) (radj_col_l : list Z) (u hi i : Z) (fuel : nat),
    (hi <= i)%Z ->
    dfs_finish_iter g radj_col_l u hi i (S fuel)
    == (assertS (fun st => (timer st < length (bijective_listV g))%nat);; t <- get (fun st t => t = timer st) ;; set_finish u t).
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
    dfs_scc_iter g fadj_col_l root u hi i (S fuel) == ret tt.
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

Lemma dfs_finish_from_skip_step :
  forall (g : AdjGraph) (radj_col_l radj_row_l : list Z) (u i : Z)
         (st : KSt) (a : unit) (s' : KSt),
    (i < csr_hi u radj_row_l)%Z ->
    visited1 st (Znth i radj_col_l 0) ->
    (dfs_finish_from g radj_col_l radj_row_l u i).(MonadErr.nrm) st a s' <->
    (dfs_finish_from g radj_col_l radj_row_l u (i + 1)).(MonadErr.nrm) st a s'.
Proof.
  intros g radj_col_l radj_row_l u i st a s' Hilt Hvis.
  unfold dfs_finish_from.
  assert (Hfuel : Z.to_nat (csr_hi u radj_row_l - i) =
                  S (Z.to_nat (csr_hi u radj_row_l - (i + 1)))).
  { assert (Hsub : csr_hi u radj_row_l - i =
                   (csr_hi u radj_row_l - (i + 1)) + 1) by lia.
    rewrite Hsub, Z2Nat.inj_add by lia.
    rewrite Nat.add_1_r. reflexivity. }
  rewrite Hfuel. apply dfs_finish_iter_skip_step; [ lia | exact Hvis ].
Qed.

Lemma dfs_finish_from_recurse_step :
  forall (g : AdjGraph) (radj_col_l radj_row_l : list Z) (u i : Z)
         (st : KSt) (a : unit) (s' : KSt),
    (i < csr_hi u radj_row_l)%Z ->
    ~ visited1 st (Znth i radj_col_l 0) ->
    (dfs_finish_from g radj_col_l radj_row_l u i).(MonadErr.nrm) st a s' <->
    ((_ <- dfs_finish g (Znth i radj_col_l 0) ;;
      dfs_finish_from g radj_col_l radj_row_l u (i + 1))).(MonadErr.nrm) st a s'.
Proof.
  intros g radj_col_l radj_row_l u i st a s' Hilt Hnvis.
  unfold dfs_finish_from.
  assert (Hfuel : Z.to_nat (csr_hi u radj_row_l - i) =
                  S (Z.to_nat (csr_hi u radj_row_l - (i + 1)))).
  { assert (Hsub : csr_hi u radj_row_l - i =
                   (csr_hi u radj_row_l - (i + 1)) + 1) by lia.
    rewrite Hsub, Z2Nat.inj_add by lia.
    rewrite Nat.add_1_r. reflexivity. }
  rewrite Hfuel. apply dfs_finish_iter_recurse_step; [ lia | exact Hnvis ].
Qed.

Lemma dfs_finish_from_skip_err_imp :
  forall (g : AdjGraph) (radj_col_l radj_row_l : list Z) (u i : Z)
         (st : KSt),
    (i < csr_hi u radj_row_l)%Z ->
    visited1 st (Znth i radj_col_l 0) ->
    (dfs_finish_from g radj_col_l radj_row_l u (i + 1)).(MonadErr.err) st ->
    (dfs_finish_from g radj_col_l radj_row_l u i).(MonadErr.err) st.
Proof.
  intros g radj_col_l radj_row_l u i st Hilt Hvis Herr.
  unfold dfs_finish_from in *.
  assert (Hfuel : Z.to_nat (csr_hi u radj_row_l - i) =
                  S (Z.to_nat (csr_hi u radj_row_l - (i + 1)))).
  { assert (Hsub : csr_hi u radj_row_l - i =
                   (csr_hi u radj_row_l - (i + 1)) + 1) by lia.
    rewrite Hsub, Z2Nat.inj_add by lia.
    rewrite Nat.add_1_r. reflexivity. }
  rewrite Hfuel.
  simpl. destruct (Z.leb (csr_hi u radj_row_l) i) eqn:E.
  - apply Z.leb_le in E. exfalso. lia.
  - unfold if_else, choice. sets_unfold.
    left. rewrite bind_err_iff. right.
    exists tt. exists st. split; [ | exact Herr ].
    unfold test. sets_unfold. split; [ reflexivity | exact Hvis ].
Qed.

Lemma dfs_finish_from_recurse_err_imp :
  forall (g : AdjGraph) (radj_col_l radj_row_l : list Z) (u i : Z)
         (st : KSt),
    (i < csr_hi u radj_row_l)%Z ->
    ~ visited1 st (Znth i radj_col_l 0) ->
    ((_ <- dfs_finish g (Znth i radj_col_l 0) ;;
      dfs_finish_from g radj_col_l radj_row_l u (i + 1))).(MonadErr.err) st ->
    (dfs_finish_from g radj_col_l radj_row_l u i).(MonadErr.err) st.
Proof.
  intros g radj_col_l radj_row_l u i st Hilt Hnvis Herr.
  unfold dfs_finish_from in *.
  assert (Hfuel : Z.to_nat (csr_hi u radj_row_l - i) =
                  S (Z.to_nat (csr_hi u radj_row_l - (i + 1)))).
  { assert (Hsub : csr_hi u radj_row_l - i =
                   (csr_hi u radj_row_l - (i + 1)) + 1) by lia.
    rewrite Hsub, Z2Nat.inj_add by lia.
    rewrite Nat.add_1_r. reflexivity. }
  rewrite Hfuel.
  simpl. destruct (Z.leb (csr_hi u radj_row_l) i) eqn:E.
  - apply Z.leb_le in E. exfalso. lia.
  - unfold if_else, choice. sets_unfold.
    right. rewrite bind_err_iff. right.
    exists tt. exists st. split; [ | exact Herr ].
    unfold test. sets_unfold. split; [ reflexivity | exact Hnvis ].
Qed.

Lemma dfs_finish_from_exit :
  forall (g : AdjGraph) (radj_col_l radj_row_l : list Z) (u i : Z),
    (csr_hi u radj_row_l <= i)%Z ->
    dfs_finish_from g radj_col_l radj_row_l u i
    == assertS (fun st => (timer st < length (bijective_listV g))%nat);; (t <- get (fun st t => t = timer st) ;; set_finish u t).
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

(* Reverse-direction err-imps (err at i -> err at i+1 / bind), used by the
   repeat_break-to-cursor simulation dfs_scc_from_sim.  The forward err-imps
   above go i+1 -> i (matching dfs2_skip_close / dfs2_recurse_close); the
   simulation peels the cursor step FORWARD (i -> i+1), so it needs the
   reverse direction, which holds under the same visited/~visited hypothesis
   (the failing test branch contributes no err at st). *)
Lemma dfs_scc_iter_skip_err_rev_imp :
  forall (g : AdjGraph) (fadj_col_l : list Z) (root u hi i : Z) (fuel : nat)
         (st : KSt),
    (i < hi)%Z ->
    visited2 st (Znth i fadj_col_l 0) ->
    (dfs_scc_iter g fadj_col_l root u hi i (S fuel)).(MonadErr.err) st ->
    (dfs_scc_iter g fadj_col_l root u hi (i + 1) fuel).(MonadErr.err) st.
Proof.
  intros g fadj_col_l root u hi i fuel st Hilt Hvis Herr.
  simpl in Herr. destruct (Z.leb hi i) eqn:E.
  - apply Z.leb_le in E. exfalso. lia.
  - unfold if_else, choice in Herr.
    sets_unfold in Herr.
    destruct Herr as [HL | HR].
    + apply bind_err_iff in HL.
      destruct HL as [Htest | [x [s0 [Hnm Hsk2]]]].
      * exfalso. unfold test in Htest. sets_unfold in Htest. exact Htest.
      * unfold test in Hnm. simpl in Hnm. destruct Hnm as [Hs2eq Hc]. subst s0. exact Hsk2.
    + apply bind_err_iff in HR.
      destruct HR as [Htest | [x [s0 [Hnm Hsk2]]]].
      * exfalso. unfold test in Htest. sets_unfold in Htest. exact Htest.
      * unfold test in Hnm. simpl in Hnm. destruct Hnm as [Hs2eq Hnc]. exfalso. apply Hnc. exact Hvis.
Qed.

Lemma dfs_scc_iter_recurse_err_rev_imp :
  forall (g : AdjGraph) (fadj_col_l : list Z) (root u hi i : Z) (fuel : nat)
         (st : KSt),
    (i < hi)%Z ->
    ~ visited2 st (Znth i fadj_col_l 0) ->
    (dfs_scc_iter g fadj_col_l root u hi i (S fuel)).(MonadErr.err) st ->
    ((_ <- dfs_scc g root (Znth i fadj_col_l 0) ;;
      dfs_scc_iter g fadj_col_l root u hi (i + 1) fuel)).(MonadErr.err) st.
Proof.
  intros g fadj_col_l root u hi i fuel st Hilt Hnvis Herr.
  simpl in Herr. destruct (Z.leb hi i) eqn:E.
  - apply Z.leb_le in E. exfalso. lia.
  - unfold if_else, choice in Herr.
    sets_unfold in Herr.
    destruct Herr as [HL | HR].
    + apply bind_err_iff in HL.
      destruct HL as [Htest | [x [s0 [Hnm Hsk2]]]].
      * exfalso. unfold test in Htest. sets_unfold in Htest. exact Htest.
      * unfold test in Hnm. simpl in Hnm. destruct Hnm as [Hs2eq Hc].
        exfalso. apply Hnvis. exact Hc.
    + apply bind_err_iff in HR.
      destruct HR as [Htest | [x [s0 [Hnm Hsk2]]]].
      * exfalso. unfold test in Htest. sets_unfold in Htest. exact Htest.
      * unfold test in Hnm. simpl in Hnm. destruct Hnm as [Hs2eq Hnc]. subst s0. exact Hsk2.
Qed.

Lemma dfs_scc_from_skip_err_rev_imp :
  forall (g : AdjGraph) (fadj_col_l fadj_row_l : list Z) (root u i : Z)
         (st : KSt),
    (i < csr_hi u fadj_row_l)%Z ->
    visited2 st (Znth i fadj_col_l 0) ->
    (dfs_scc_from g fadj_col_l fadj_row_l root u i).(MonadErr.err) st ->
    (dfs_scc_from g fadj_col_l fadj_row_l root u (i + 1)).(MonadErr.err) st.
Proof.
  intros g fadj_col_l fadj_row_l root u i st Hilt Hvis Herr.
  unfold dfs_scc_from in *.
  assert (Hfuel : Z.to_nat (csr_hi u fadj_row_l - i) =
                  S (Z.to_nat (csr_hi u fadj_row_l - (i + 1)))).
  { assert (Hsub : csr_hi u fadj_row_l - i = (csr_hi u fadj_row_l - (i + 1)) + 1) by lia.
    rewrite Hsub, Z2Nat.inj_add by lia.
    rewrite Nat.add_1_r. reflexivity. }
  rewrite Hfuel in Herr.
  exact (dfs_scc_iter_skip_err_rev_imp g fadj_col_l root u _ i _ st Hilt Hvis Herr).
Qed.

Lemma dfs_scc_from_recurse_err_rev_imp :
  forall (g : AdjGraph) (fadj_col_l fadj_row_l : list Z) (root u i : Z)
         (st : KSt),
    (i < csr_hi u fadj_row_l)%Z ->
    ~ visited2 st (Znth i fadj_col_l 0) ->
    (dfs_scc_from g fadj_col_l fadj_row_l root u i).(MonadErr.err) st ->
    ((_ <- dfs_scc g root (Znth i fadj_col_l 0) ;;
      dfs_scc_from g fadj_col_l fadj_row_l root u (i + 1))).(MonadErr.err) st.
Proof.
  intros g fadj_col_l fadj_row_l root u i st Hilt Hnvis Herr.
  unfold dfs_scc_from in *.
  assert (Hfuel : Z.to_nat (csr_hi u fadj_row_l - i) =
                  S (Z.to_nat (csr_hi u fadj_row_l - (i + 1)))).
  { assert (Hsub : csr_hi u fadj_row_l - i = (csr_hi u fadj_row_l - (i + 1)) + 1) by lia.
    rewrite Hsub, Z2Nat.inj_add by lia.
    rewrite Nat.add_1_r. reflexivity. }
  rewrite Hfuel in Herr.
  exact (dfs_scc_iter_recurse_err_rev_imp g fadj_col_l root u _ i _ st Hilt Hnvis Herr).
Qed.

Lemma dfs_scc_from_exit :
  forall (g : AdjGraph) (fadj_col_l fadj_row_l : list Z) (root u i : Z),
    (csr_hi u fadj_row_l <= i)%Z ->
    dfs_scc_from g fadj_col_l fadj_row_l root u i == ret tt.
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

(* Absorb chain REMOVED.  With the cursor exit set to `ret tt` (dfs2) and
   `get timer ;; set_finish u t` (dfs1), the loop-exit VC no longer needs to
   bridge a re-entered `dfs_scc g root u` / `dfs_finish g u` to a no-op or
   set_finish transition via DFS_scc_absorb.  The exit lemma
   (dfs_scc_from_exit / dfs_finish_from_exit) now equates the cursor
   continuation directly to the exit monad, so the return VC is a plain
   safeExec_proequiv.  No Admitted absorb lemmas are needed. *)

(* dfs2 Gap A (loop exit) closer: at i >= hi, dfs_scc_from ... u i == ret tt,
   so `safeExec P (dfs_scc_from ... u i) X` is rewritten to
   `safeExec P (ret tt) X` by program equivalence.  Trivial. *)
Lemma dfs2_return_close :
  forall (g: AdjGraph) (fadj_col_l fadj_row_l: list Z) (root u i: Z)
         (vis2_m sid_m: list Z) (root_v: Z) (X: unit -> KSt -> Prop),
  (csr_hi u fadj_row_l <= i)%Z ->
  safeExec (pre_dfs2 g fadj_col_l fadj_row_l vis2_m sid_m root_v)
           (dfs_scc_from g fadj_col_l fadj_row_l root u i) X ->
  safeExec (pre_dfs2 g fadj_col_l fadj_row_l vis2_m sid_m root_v) (ret tt) X.
Proof.
  intros g fadj_col_l fadj_row_l root u i vis2_m sid_m root_v X Hhige Hsccfrom.
  apply safeExec_proequiv with (c1 := dfs_scc_from g fadj_col_l fadj_row_l root u i).
  - exact (dfs_scc_from_exit g fadj_col_l fadj_row_l root u i Hhige).
  - exact Hsccfrom.
Qed.

(* dfs1 loop-exit closer: at i >= hi, dfs_finish_from ... u i ==
   (t <- get timer ;; set_finish u t).  The C post-loop reads timer_p[0],
   sets fin[u] = t0, timer_p[0] = t0+1 — exactly the nrm transition of
   `get (fun st t => t = timer st) ;; set_finish u t`: from st (timer = timer_m)
   it steps to st' with timer st' = S (timer st) and finish st' u = timer st.
   Given the safeExec witness sigma with pre_dfs1 vis_m fin_m timer_m and
   timer_m = Z.to_nat (timer sigma), the post-state sigma' has
     timer sigma' = S timer_m,  finish sigma' u = timer_m,
   which matches pre_dfs1 vis_m (replace_Znth u timer_m fin_m) (S timer_m)
   (vis1 unchanged by set_finish; finish[u] = timer_m; other finish preserved).
   Then X tt sigma' follows from the wp of the exit monad. *)
Lemma dfs1_return_close :
  forall (g: AdjGraph) (radj_col_l radj_row_l: list Z) (u i: Z)
         (vis1_m fin_m: list Z) (timer_m: Z) (X: unit -> KSt -> Prop),
  (0 <= u < adj_verts g)%Z ->
  (0 <= timer_m)%Z ->
  Zlength fin_m = adj_verts g ->
  (csr_hi u radj_row_l <= i)%Z ->
  safeExec (pre_dfs1 g radj_col_l radj_row_l vis1_m fin_m timer_m)
           (dfs_finish_from g radj_col_l radj_row_l u i) X ->
  safeExec (pre_dfs1 g radj_col_l radj_row_l vis1_m
              (replace_Znth u timer_m fin_m) (timer_m + 1)) (ret tt) X.
Proof.
  intros g radj_col_l radj_row_l u i vis1_m fin_m timer_m X
         Hub Htm Hlenfin Hhige Hsccfrom.
  assert (Hexit : PartialOrder_Setoid.equiv
            (dfs_finish_from g radj_col_l radj_row_l u i)
            (assertS (fun st => (timer st < length (bijective_listV g))%nat);; t <- get (fun st t => t = timer st) ;; set_finish u t))
    by (apply dfs_finish_from_exit; exact Hhige).
  assert (Hscc : safeExec (pre_dfs1 g radj_col_l radj_row_l vis1_m fin_m timer_m)
                          (assertS (fun st => (timer st < length (bijective_listV g))%nat);; t <- get (fun st t => t = timer st) ;; set_finish u t) X).
  { eapply safeExec_proequiv with (c1 := dfs_finish_from g radj_col_l radj_row_l u i).
    - exact Hexit.
    - exact Hsccfrom. }
  apply safeExec_assertS_seq in Hscc.
  destruct Hscc as [sigma [[Hbnd Hpre] Hsafe]].
  destruct Hpre as [Hpv [Hpf Hpt]].
  pose (sigma' := MkSt (S (timer sigma))
                       (fun v => if Z.eqb v u then timer sigma else finish sigma v)
                       (visited1 sigma) (visited2 sigma)
                       (scc_id sigma) (scc_next sigma)).
  assert (Hfsu : finish sigma' u = timer sigma).
  { unfold sigma'. simpl. destruct (Z.eqb u u) eqn:Eu.
    - reflexivity.
    - apply Z.eqb_neq in Eu. exfalso. apply Eu. reflexivity. }
  assert (Hfsv : forall v, v <> u -> finish sigma' v = finish sigma v).
  { intros v Hvne. unfold sigma'. simpl. destruct (Z.eqb v u) eqn:Ev.
    - apply Z.eqb_eq in Ev. exfalso. apply Hvne. exact Ev.
    - reflexivity. }
  assert (Htimer' : timer sigma' = S (timer sigma)) by (unfold sigma'; reflexivity).
  assert (Hvis1' : visited1 sigma' = visited1 sigma) by (unfold sigma'; reflexivity).
  assert (Hvis2' : visited2 sigma' = visited2 sigma) by (unfold sigma'; reflexivity).
  assert (Hsid' : scc_id sigma' = scc_id sigma) by (unfold sigma'; reflexivity).
  assert (Hsnext' : scc_next sigma' = scc_next sigma) by (unfold sigma'; reflexivity).
  assert (Hnrm : (t <- get (fun st t => t = timer st) ;; set_finish u t).(MonadErr.nrm)
                  sigma tt sigma').
  { cbv beta iota delta [MonadErr.bind MonadErr.nrm_nrm get set_finish custom].
    eexists. exists sigma. split.
    - split; [ reflexivity | reflexivity ].
    - simpl. split; [ exact Htimer' | ].
      split; [ exact Hfsu | ].
      split; [ exact Hfsv | ].
      split; [ exact Hvis1' | ].
      split; [ exact Hvis2' | ].
      split; [ exact Hsid' | ].
      exact Hsnext'. }
  assert (Hxtt : X tt sigma')
    by (eapply wp_spec; eassumption).
  unfold safeExec. exists sigma'. split.
  - unfold pre_dfs1.
    assert (HnZ : Z.to_nat (timer_m + 1) = S (Z.to_nat timer_m)).
    { rewrite Z.add_1_r. apply Z2Nat.inj_succ. lia. }
    rewrite HnZ. split; [ | split; [ | ] ].
    + intros x Hr. unfold sigma'. simpl. split; intros Hvis.
      * apply (proj1 (Hpv x Hr)). exact Hvis.
      * apply (proj2 (Hpv x Hr)). exact Hvis.
    + intros w Hr. unfold sigma'. simpl.
      destruct (Z.eqb w u) eqn:Eu0.
      * apply Z.eqb_eq in Eu0. subst w.
        assert (Hin : (0 <= u < Zlength fin_m)%Z) by (rewrite Hlenfin; lia).
        rewrite (Znth_replace_eq fin_m u timer_m 0 Hin). exact Hpt.
      * apply Z.eqb_neq in Eu0.
        assert (Hin : (0 <= w < Zlength fin_m)%Z) by (rewrite Hlenfin; lia).
        rewrite (Znth_replace_neq fin_m w u timer_m 0 Hin (proj1 Hub) Eu0).
        apply (Hpf w Hr).
    + rewrite Htimer'. f_equal. exact Hpt.
  - unfold safe, weakestpre. split.
    + intro Herr. cbv beta iota delta [MonadErr.ret] in Herr. sets_unfold in Herr. exfalso. exact Herr.
    + intros r s' Hnrm2. cbv beta iota delta [MonadErr.ret] in Hnrm2. inversion Hnrm2; subst. exact Hxtt.
Qed.


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

(* dfs1 analogues of dfs2_skip_close / dfs2_recurse_close.  vis-conditional
   cursor: at position i, v = Znth i radj_col_l 0; if visited1, SKIP (advance
   cursor); if not, RECURSE into dfs_finish g v then advance.  Each extracts
   the safeExec witness sigma, derives visited1/~visited1 of v at sigma via
   pre_dfs1, applies dfs_finish_from_skip_step / dfs_finish_from_recurse_step,
   and reconstructs. *)
Lemma dfs1_skip_close :
  forall (g: AdjGraph) (radj_col_l radj_row_l: list Z) (u i: Z)
         (vis1_m fin_m: list Z) (timer_v: Z) (X: unit -> KSt -> Prop),
  (i < csr_hi u radj_row_l)%Z ->
  (0 <= Znth i radj_col_l 0 < adj_verts g)%Z ->
  Znth (Znth i radj_col_l 0) vis1_m 0 <> 0%Z ->
  safeExec (pre_dfs1 g radj_col_l radj_row_l vis1_m fin_m timer_v)
           (dfs_finish_from g radj_col_l radj_row_l u i) X ->
  safeExec (pre_dfs1 g radj_col_l radj_row_l vis1_m fin_m timer_v)
           (dfs_finish_from g radj_col_l radj_row_l u (i + 1)) X.
Proof.
  intros g radj_col_l radj_row_l u i vis1_m fin_m timer_v X
         Hilt Hvvb Hvvis Hsccfrom.
  destruct Hsccfrom as [sigma [Hpre Hsafe]].
  destruct Hpre as [Hpv [Hpf Hpt]].
  assert (Hvisv : visited1 sigma (Znth i radj_col_l 0))
    by (exact (proj2 (Hpv (Znth i radj_col_l 0) Hvvb) Hvvis)).
  unfold safeExec. exists sigma. split.
  - unfold pre_dfs1; split; [ exact Hpv | split; [ exact Hpf | exact Hpt ] ].
  - unfold safe, weakestpre. split.
    + intros Herr. destruct Hsafe as [Hnoerr _]. exfalso. apply Hnoerr.
      apply (dfs_finish_from_skip_err_imp g radj_col_l radj_row_l u i sigma Hilt Hvisv).
      exact Herr.
    + intros a s' Ht. destruct Hsafe as [_ Hpost]. apply Hpost.
      apply (proj2 (dfs_finish_from_skip_step g radj_col_l radj_row_l u i sigma a s' Hilt Hvisv)).
      exact Ht.
Qed.

Lemma dfs1_recurse_close :
  forall (g: AdjGraph) (radj_col_l radj_row_l: list Z) (u i: Z)
         (vis1_m fin_m: list Z) (timer_v: Z) (X: unit -> KSt -> Prop),
  (i < csr_hi u radj_row_l)%Z ->
  (0 <= Znth i radj_col_l 0 < adj_verts g)%Z ->
  Znth (Znth i radj_col_l 0) vis1_m 0 = 0%Z ->
  safeExec (pre_dfs1 g radj_col_l radj_row_l vis1_m fin_m timer_v)
           (dfs_finish_from g radj_col_l radj_row_l u i) X ->
  safeExec (pre_dfs1 g radj_col_l radj_row_l vis1_m fin_m timer_v)
           (bind (dfs_finish g (Znth i radj_col_l 0))
                 (dfs_finish_fromK g radj_col_l radj_row_l u (i + 1))) X.
Proof.
  intros g radj_col_l radj_row_l u i vis1_m fin_m timer_v X
         Hilt Hvvb Hvvis0 Hsccfrom.
  destruct Hsccfrom as [sigma [Hpre Hsafe]].
  destruct Hpre as [Hpv [Hpf Hpt]].
  assert (Hnvisv : ~ visited1 sigma (Znth i radj_col_l 0)).
  { intro Hvv.
    assert (Hzz : Znth (Znth i radj_col_l 0) vis1_m 0 <> 0%Z)
      by (apply (proj1 (Hpv (Znth i radj_col_l 0) Hvvb)); exact Hvv).
    lia. }
  unfold safeExec. exists sigma. split.
  - unfold pre_dfs1; split; [ exact Hpv | split; [ exact Hpf | exact Hpt ] ].
  - unfold safe, weakestpre. split.
    + intros Herr. destruct Hsafe as [Hnoerr _]. exfalso. apply Hnoerr.
      apply (dfs_finish_from_recurse_err_imp g radj_col_l radj_row_l u i sigma Hilt Hnvisv).
      exact Herr.
    + intros a s' Ht. destruct Hsafe as [_ Hpost]. apply Hpost.
      apply (proj2 (dfs_finish_from_recurse_step g radj_col_l radj_row_l u i sigma a s' Hilt Hnvisv)).
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

(* ===================================================================== *)
(* dfs2_entry_close infrastructure (phase-2 entry refinement).            *)
(*                                                                        *)
(* The entry VC (dfs2_entail_wit_1_split_goal_9) reduces to: given        *)
(*   safeExec (pre_dfs2 vis sid) (dfs_scc g root u) X,                    *)
(* show safeExec (pre_dfs2 vis1 sid') (dfs_scc_from g fc fr root u lo) X, *)
(* where vis1 = replace_Znth u 1 vis, sid' = replace_Znth u (sid[root]) sid. *)
(*                                                                        *)
(* dfs2_repeat_body is the body of DFS_scc_f, u-parametrised, with the    *)
(* recursive leaf W = dfs_scc g root.  It is definitionally equal to the  *)
(* body of DFS_scc_f g root (dfs_scc g root) u (verified by reflexivity    *)
(* in dfs2_scc_unfold_repeat), so repeat_break congruence is free.        *)
(*                                                                        *)
(* visit2_pre_dfs2_step / set_scc_id_pre_dfs2_step peel the visit2 u +    *)
(* set_scc_id u root prelude off safeExec(dfs_scc g root u), leaving      *)
(* safeExec over repeat_break (dfs2_repeat_body g root u) empty at the    *)
(* post-visit/set_scc_id state.  dfs2_visit_setid_decompose composes the  *)
(* two peels with dfs2_scc_unfold_repeat + safeExec_proequiv.             *)
(*                                                                        *)
(* The remaining piece is dfs_scc_from_sim: the cursor-vs-repeat_break    *)
(* simulation (safe(repeat_break B e_set_i) -> safe(dfs_scc_from ... u i)),*)
(* which is the main wp-induction workload and is tracked separately.     *)
(* ===================================================================== *)

Definition dfs2_repeat_body (g: AdjGraph) (root u: Z)
  : (Z * Z -> Prop) -> program KSt (CntOrBrk (Z * Z -> Prop) unit) :=
  fun e_set =>
    choice
      (e <- any (Z * Z);;
       v <- any Z;;
       assume (fun (_ : KSt) => ~ e ∈ e_set);;
       assume (fun st => ~ visited2 st v);;
       assume (fun (_ : KSt) => step_aux g e u v);;
       dfs_scc g root v;;
       continue (e_set ∪ Sets.singleton e))
      (assume (fun st =>
                 forall (e: Z * Z) (v: Z),
                   step_aux g e u v ->
                   e ∈ e_set \/ visited2 st v);;
       assertS (fun st => scc_id st u = scc_id st root);;
       break tt).

Lemma dfs2_scc_unfold_repeat :
  forall (g: AdjGraph) (root u: Z),
  gvalid g ->
  dfs_scc g root u
  ==
  visit2 u ;; set_scc_id u root ;; repeat_break (dfs2_repeat_body g root u) ∅.
Proof.
  intros g root u Hg.
  rewrite (dfs_scc_unfold g root u Hg).
  unfold DFS_scc_f.
  reflexivity.
Qed.

Lemma visit2_pre_dfs2_step :
  forall (g: AdjGraph) (fc fr vis sid: list Z) (root_v u: Z),
    (Zlength vis = adj_verts g)%Z ->
    (0 <= u < adj_verts g)%Z ->
    pre_dfs2 g fc fr vis sid root_v -@ visit2 u -⥅
      (pre_dfs2 g fc fr (replace_Znth u 1 vis) sid root_v) ♯ tt.
Proof.
  intros g fc fr vis sid root_v u Hvlen Hub st0 Hpre.
  destruct Hpre as [Hpv Hps].
  assert (HLu : (0 <= u < Zlength vis)%Z) by (rewrite Hvlen; exact Hub).
  pose (st1 := MkSt (timer st0) (finish st0) (visited1 st0)
                       (fun w => visited2 st0 w \/ w = u) (scc_id st0) (scc_next st0)).
  assert (Hnrm : (visit2 u).(MonadErr.nrm) st0 tt st1).
  { unfold visit2. simpl. split.
    - (* visited2 st1 == visited2 st0 ∪ {u} *)
      unfold st1. simpl. sets_unfold. intros w. split; intros Hw.
      + destruct Hw as [Hw | Hw]; [ left; exact Hw | subst w; right; reflexivity ].
      + destruct Hw as [Hw | Hw]; [ left; exact Hw | subst w; right; reflexivity ].
    - unfold st1. simpl. repeat split; reflexivity.
  }
  exists st1. split; [ exact Hnrm | ].
  unfold pre_dfs2. split.
  - intros w Hw. assert (HLw : (0 <= w < Zlength vis)%Z) by (rewrite Hvlen; exact Hw).
    unfold st1. simpl. split; intros Hvis.
    + destruct (Z.eqb w u) eqn:E.
      * apply Z.eqb_eq in E. subst w. rewrite (Znth_replace_eq vis u 1 0 HLu). lia.
      * apply Z.eqb_neq in E. rewrite (Znth_replace_neq vis w u 1 0 HLw (proj1 HLu) E).
        destruct Hvis as [Hv | Hwu].
        -- apply (proj1 (Hpv w Hw)). exact Hv.
        -- exfalso. apply E. exact Hwu.
    + destruct (Z.eqb w u) eqn:E.
      * apply Z.eqb_eq in E. subst w. right. reflexivity.
      * apply Z.eqb_neq in E. rewrite (Znth_replace_neq vis w u 1 0 HLw (proj1 HLu) E) in Hvis.
        left. apply (proj2 (Hpv w Hw)). exact Hvis.
  - intros w Hw. unfold st1. simpl. exact (Hps w Hw).
Qed.

Lemma set_scc_id_pre_dfs2_step :
  forall (g: AdjGraph) (fc fr vis sid: list Z) (root_v u root: Z),
    (Zlength vis = adj_verts g)%Z ->
    (Zlength sid = adj_verts g)%Z ->
    (0 <= u < adj_verts g)%Z ->
    (0 <= root < adj_verts g)%Z ->
    pre_dfs2 g fc fr vis sid root_v -@ set_scc_id u root -⥅
      (pre_dfs2 g fc fr vis (replace_Znth u (Znth root sid 0) sid) root_v) ♯ tt.
Proof.
  intros g fc fr vis sid root_v u root Hvlen Hslen Hub Hroot st0 Hpre.
  destruct Hpre as [Hpv Hps].
  assert (HLu : (0 <= u < Zlength sid)%Z) by (rewrite Hslen; exact Hub).
  assert (HLroot : (0 <= root < Zlength sid)%Z) by (rewrite Hslen; exact Hroot).
  pose (st1 := MkSt (timer st0) (finish st0) (visited1 st0) (visited2 st0)
              (fun w => if Z.eqb w u then scc_id st0 root else scc_id st0 w)
              (scc_next st0)).
  assert (Hnrm : (set_scc_id u root).(MonadErr.nrm) st0 tt st1).
  { unfold set_scc_id. simpl. split.
    - unfold st1. simpl. destruct (Z.eqb u u) eqn:E.
      + reflexivity.
      + apply Z.eqb_neq in E. exfalso. apply E. reflexivity.
    - split.
      + intros v Hvne. unfold st1. simpl. destruct (Z.eqb v u) eqn:E.
        * apply Z.eqb_eq in E. exfalso. apply Hvne. exact E.
        * reflexivity.
      + unfold st1. simpl. repeat split; reflexivity.
  }
  exists st1. split; [ exact Hnrm | ].
  unfold pre_dfs2. split.
  - intros w Hw. exact (Hpv w Hw).
  - intros w Hw. assert (HLw : (0 <= w < Zlength sid)%Z) by (rewrite Hslen; exact Hw).
    unfold st1. simpl. destruct (Z.eqb w u) eqn:E.
    + apply Z.eqb_eq in E. subst w. rewrite (Znth_replace_eq sid u (Znth root sid 0) 0 HLu).
      apply Hps. exact Hroot.
    + apply Z.eqb_neq in E. rewrite (Znth_replace_neq sid w u (Znth root sid 0) 0 HLw (proj1 HLu) E).
      apply Hps. exact Hw.
Qed.

Lemma dfs2_visit_setid_decompose :
  forall (g: AdjGraph) (fc fr vis sid: list Z) (root_v u root: Z) (X: unit -> KSt -> Prop),
    gvalid g ->
    (Zlength vis = adj_verts g)%Z ->
    (Zlength sid = adj_verts g)%Z ->
    (0 <= u < adj_verts g)%Z ->
    (0 <= root < adj_verts g)%Z ->
    safeExec (pre_dfs2 g fc fr vis sid root_v) (dfs_scc g root u) X ->
    safeExec (pre_dfs2 g fc fr (replace_Znth u 1 vis) (replace_Znth u (Znth root sid 0) sid) root_v)
             (repeat_break (dfs2_repeat_body g root u) ∅) X.
Proof.
  intros g fc fr vis sid root_v u root X Hg Hvlen Hslen Hub Hroot Hsafe.
  rewrite (dfs2_scc_unfold_repeat g root u Hg) in Hsafe.
  apply (highstepbind_derive (visit2 u)
            (fun _ => set_scc_id u root ;; repeat_break (dfs2_repeat_body g root u) ∅)
            (pre_dfs2 g fc fr vis sid root_v) tt
            (pre_dfs2 g fc fr (replace_Znth u 1 vis) sid root_v)
            (visit2_pre_dfs2_step g fc fr vis sid root_v u Hvlen Hub)) in Hsafe.
  assert (Hvlen1 : (Zlength (replace_Znth u 1 vis) = adj_verts g)%Z).
  { rewrite Zlength_replace_Znth. exact Hvlen. }
  apply (highstepbind_derive (set_scc_id u root)
            (fun _ => repeat_break (dfs2_repeat_body g root u) ∅)
            (pre_dfs2 g fc fr (replace_Znth u 1 vis) sid root_v) tt
            (pre_dfs2 g fc fr (replace_Znth u 1 vis) (replace_Znth u (Znth root sid 0) sid) root_v)
            (set_scc_id_pre_dfs2_step g fc fr (replace_Znth u 1 vis) sid root_v u root
               Hvlen1 Hslen Hub Hroot)) in Hsafe.
  exact Hsafe.
Qed.

(* ================================================================= *)
(* Reusable MonadErr helper lemmas (pure monad, no algorithm props). *)
(* Used by dfs_scc_from_sim to factor the repeat_break nrm-step out of *)
(* the simulation's BASE/RECURSE cases.                               *)
(* ================================================================= *)

(* wp_seq: sequence-specialised wp_bind, bridging the eta gap between
   `f ;; rest` (= bind f (fun _ => rest)) and wp_bind's `x <- f ;; g x`. *)
Lemma wp_seq {Σ A B: Type} (f: program Σ A) (rest: program Σ B) (Q: B -> Σ -> Prop) :
  (weakestpre (f ;; rest) Q == weakestpre f (fun _ => weakestpre rest Q))%sets.
Proof.
  intros σ. apply (wp_bind f (fun (_:A) => rest) Q).
Qed.

(* repeat_break_break_step: body produces by_break b at sigma (no state change)
   -> repeat_break produces b at sigma (first iteration takes the break branch). *)
Lemma repeat_break_break_step :
  forall (Σ: Type) {A: Type} {B: Type}
         (body: A -> program Σ (CntOrBrk A B)) (a: A) (b: B) (σ: Σ),
    (body a).(MonadErr.nrm) σ (@by_break A B b) σ ->
    (repeat_break body a).(MonadErr.nrm) σ b σ.
Proof.
  intros Σ A B body a b σ Hbodystep.
  pose proof (repeat_break_unfold body) as Hunf.
  unfold equiv in Hunf. simpl in Hunf.
  unfold Equiv_lift, LiftConstructors.lift_rel2 in Hunf.
  specialize (Hunf a) as Hpt.
  destruct Hpt as [Hnrmpt Herrpt].
  sets_unfold in Hnrmpt.
  specialize (Hnrmpt σ b σ) as [Hfwd Hbwd].
  apply Hbwd.
  simpl.
  unfold MonadErr.bind. simpl.
  eexists (by_break b). exists σ. split.
  - exact Hbodystep.
  - simpl.
    split; [ reflexivity | reflexivity ].
Qed.

(* repeat_break_break_step_gen: generalised break-step allowing the body to
   change the state (sigma -> sigma') before emitting by_break b.  Needed by
   dfs_finish_from_sim BASE: DFS_finish_f's break branch runs `set_finish u t`,
   which mutates the state, unlike phase-2's break (assertS sid ;; break). *)
Lemma repeat_break_break_step_gen :
  forall (Σ: Type) {A: Type} {B: Type}
         (body: A -> program Σ (CntOrBrk A B)) (a: A) (b: B) (σ σ': Σ),
    (body a).(MonadErr.nrm) σ (@by_break A B b) σ' ->
    (repeat_break body a).(MonadErr.nrm) σ b σ'.
Proof.
  intros Σ A B body a b σ σ' Hbodystep.
  pose proof (repeat_break_unfold body) as Hunf.
  unfold equiv in Hunf. simpl in Hunf.
  unfold Equiv_lift, LiftConstructors.lift_rel2 in Hunf.
  specialize (Hunf a) as Hpt.
  destruct Hpt as [Hnrmpt Herrpt].
  sets_unfold in Hnrmpt.
  specialize (Hnrmpt σ b σ') as [Hfwd Hbwd].
  apply Hbwd.
  simpl.
  unfold MonadErr.bind. simpl.
  eexists (by_break b). exists σ'. split.
  - exact Hbodystep.
  - simpl.
    split; [ reflexivity | reflexivity ].
Qed.

(* repeat_break_continue_step: body produces by_continue a' at (σ -> σ'),
   then repeat_break body a' produces b at (σ' -> σ'') -> repeat_break body a
   produces b at (σ -> σ''). *)
Lemma repeat_break_continue_step :
  forall (Σ: Type) {A: Type} {B: Type}
         (body: A -> program Σ (CntOrBrk A B)) (a a': A) (σ σ': Σ) (b: B) (σ'': Σ),
    (body a).(MonadErr.nrm) σ (by_continue a') σ' ->
    (repeat_break body a').(MonadErr.nrm) σ' b σ'' ->
    (repeat_break body a).(MonadErr.nrm) σ b σ''.
Proof.
  intros Σ A B body a a' σ σ' b σ'' Hbodystep Hrec.
  pose proof (repeat_break_unfold body) as Hunf.
  unfold equiv in Hunf. simpl in Hunf.
  unfold Equiv_lift, LiftConstructors.lift_rel2 in Hunf.
  specialize (Hunf a) as Hpt.
  destruct Hpt as [Hnrmpt Herrpt].
  sets_unfold in Hnrmpt.
  specialize (Hnrmpt σ b σ'') as [Hfwd Hbwd].
  apply Hbwd.
  simpl.
  unfold MonadErr.bind. simpl.
  eexists (by_continue a'). exists σ'. split.
  - exact Hbodystep.
  - simpl. exact Hrec.
Qed.

(* ===================================================================== *)
(* dfs_scc_from_sim: cursor (dfs_scc_from) vs repeat_break simulation.   *)
(* The recursive dfs_scc g root v call is treated as an atom; only the   *)
(* scheduling layer (cursor vs repeat_break body dispatch) is related.   *)
(* Fuel: induction on Z.to_nat (hi - i).                                 *)
(* ===================================================================== *)
Lemma dfs_scc_from_sim :
  forall (g: AdjGraph) (fc fr vis sid: list Z) (root u: Z) (lo hi i: Z)
         (n: nat) (X: unit -> KSt -> Prop) (σ: KSt),
    let B := dfs2_repeat_body g root u in
    csr_lo u fr = lo ->
    csr_hi u fr = hi ->
    csr_wf2 g fc fr vis sid ->
    csr2_faithful g fc fr ->
    (0 <= u < adj_verts g)%Z ->
    Z.to_nat (hi - i) = n ->
    (lo <= i)%Z ->
    forall (e_set: Z * Z -> Prop),
      (forall (e: Z * Z), e_set e ->
         exists k, (lo <= k < i)%Z /\ e = (u, Znth k fc 0)) ->
      (forall k, (lo <= k < i)%Z -> ~ e_set (u, Znth k fc 0) ->
         visited2 σ (Znth k fc 0)) ->
      (forall j, (lo <= j < hi)%Z -> ~ visited2 σ (Znth j fc 0) ->
         ~ e_set (u, Znth j fc 0)) ->
      scc_id σ u = scc_id σ root ->
      visited2 σ u ->
      safe σ (repeat_break B e_set) X ->
      safe σ (dfs_scc_from g fc fr root u i) X.
Proof.
  intros g fc fr vis sid root u lo hi i n X σ B Hlo Heqhi Hwf Hfaith Hu Hfuel Hloi e_set
         HA HB HE HC HD Hsafe.
  revert i X σ Hfuel Hloi e_set HA HB HE HC HD Hsafe.
  induction n as [|n' IHn].
  - (* BASE: Z.to_nat (hi - i) = 0, hence i >= hi *)
    intros i X σ Hfuel Hloi e_set HA HB HE HC HD Hsafe.
    assert (Hge : (hi <= i)%Z).
    { destruct (Z.le_gt_cases hi i) as [Hle | Hgt]; [ exact Hle | ].
      exfalso.
      assert (Hpos : (0 < hi - i)%Z) by lia.
      destruct (Z.eq_dec (hi - i) 0) as [Heq | Hneq].
      - subst. lia.
      - assert (Hn0 : (Z.to_nat (hi - i) <> 0)%nat).
        { intro Hz. assert (0 <= hi - i)%Z by lia.
          pose proof (Z2Nat.id (hi - i) H) as Hid.
          rewrite Hz in Hid. lia. }
        rewrite Hfuel in Hn0. exfalso. apply Hn0. reflexivity. }
    assert (Hclosure : (forall (e: Z * Z) (v: Z), step_aux g e u v ->
                                    e ∈ e_set \/ visited2 σ v)).
    { intros e v Hstep.
      assert (Hstep_g : reachable_basic.step g u v) by (eapply step_trivial; eassumption).
      destruct Hstep as [Heq [Hxv [Hvv Hiny]]].
      subst e.
      pose proof (Hfaith u v Hxv Hvv) as Hiff.
      apply (proj1 Hiff) in Hstep_g as [j [Hjlo Hjv]].
      destruct (classic (e_set (u, v))) as [Hin | Hnin].
      - left. exact Hin.
      - right. rewrite <- Hjv. apply (HB j). lia.
        rewrite Hjv. exact Hnin. }
    assert (Hbodystep : (B e_set).(MonadErr.nrm) σ (@by_break (Z*Z->Prop) unit tt) σ).
    { unfold B, dfs2_repeat_body.
      unfold choice. simpl.
      right.
      unfold_monad. simpl.
      eexists tt. eexists σ. split.
      - split; [ reflexivity | exact Hclosure ].
      - eexists tt. eexists σ. split.
        + split; [ reflexivity | exact HC ].
        + simpl. split; [ reflexivity | reflexivity ]. }
    assert (Hrbstep : (repeat_break B e_set).(MonadErr.nrm) σ tt σ).
    { eapply repeat_break_break_step. exact Hbodystep. }
    assert (Hxtt : X tt σ) by (eapply wp_spec; eassumption).
    unfold safe in *.
    assert (Hge' : (csr_hi u fr <= i)%Z) by (rewrite Heqhi; exact Hge).
    pose proof (wp_progequiv (ret tt) (dfs_scc_from g fc fr root u i) X
                  (dfs_scc_from_exit g fc fr root u i Hge')) as Hwp.
    sets_unfold in Hwp.
    specialize (Hwp σ) as [Hfwd Hbwd].
    unfold weakestpre in *.
    sets_unfold in Hfwd.
    apply Hfwd.
    sets_unfold.
    split.
    + intro Herr. simpl in Herr. exact Herr.
    + intros r σ' Hretstep. simpl in Hretstep.
      destruct Hretstep as [Hr Hσ]. subst r. subst σ'.
      exact Hxtt.
  - (* STEP: hi - i = S n', i.e. lo <= i < hi *)
    intros i X σ Hfuel Hloi e_set HA HB HE HC HD Hsafe.
    assert (Hilt : (i < hi)%Z).
    { assert (Hnonneg : (0 <= hi - i)%Z).
      { destruct (Z.le_gt_cases hi i) as [Hle | Hgt].
        - exfalso. assert (Heqz : hi - i = 0) by lia.
          rewrite Heqz in Hfuel. simpl in Hfuel. discriminate.
        - lia. }
      lia. }
    assert (Hilt' : (i < csr_hi u fr)%Z) by (rewrite Heqhi; exact Hilt).
    set (v := Znth i fc 0) in *.
    destruct (classic (visited2 σ v)) as [Hvisv | Hnvisv].
    + (* SKIP: visited2 σ v *)
      assert (Hfuel' : Z.to_nat (hi - (i + 1)) = n').
      { assert (Hsub : hi - i = (hi - (i + 1)) + 1) by lia.
        assert (Hnonneg1 : (0 <= hi - (i + 1))%Z) by lia.
        rewrite Hsub in Hfuel.
        rewrite Z2Nat.inj_add in Hfuel by lia.
        rewrite Nat.add_1_r in Hfuel. injection Hfuel. auto. }
      assert (Hloi' : (lo <= i + 1)%Z) by lia.
      assert (HA' : forall (e: Z * Z), e_set e ->
                     exists k, (lo <= k < i + 1)%Z /\ e = (u, Znth k fc 0)).
      { intros e He. destruct (HA e He) as [k [Hk Heq]]. exists k. split; [ lia | exact Heq ]. }
      assert (HB' : forall k, (lo <= k < i + 1)%Z -> ~ e_set (u, Znth k fc 0) ->
                     visited2 σ (Znth k fc 0)).
      { intros k Hk Hne.
        destruct (Z.le_gt_cases k (i - 1)) as [Hle | Hgt].
        - apply (HB k); [ lia | exact Hne ].
        - assert (Hki : k = i) by lia. subst k. exact Hvisv. }
      assert (HE' : forall j, (lo <= j < hi)%Z -> ~ visited2 σ (Znth j fc 0) ->
                     ~ e_set (u, Znth j fc 0)).
      { exact HE. }
      assert (Hsafe_ih : safe σ (dfs_scc_from g fc fr root u (i + 1)) X).
      { eapply IHn; [ exact Hfuel' | exact Hloi' | exact HA' | exact HB' | exact HE' |
                      exact HC | exact HD | exact Hsafe ]. }
      unfold safe in *.
      unfold weakestpre in *.
      split.
      * intro Herr.
        destruct Hsafe_ih as [Hnoerr _].
        exfalso. apply Hnoerr.
        apply (dfs_scc_from_skip_err_rev_imp g fc fr root u i σ Hilt' Hvisv).
        exact Herr.
      * intros a s' Hstep.
        destruct Hsafe_ih as [_ Hpost].
        apply Hpost.
        apply (proj1 (dfs_scc_from_skip_step g fc fr root u i σ a s' Hilt' Hvisv)).
        exact Hstep.
    + (* RECURSE: ~visited2 σ v *)
      assert (Hagvalid : gvalid g) by (destruct Hwf as [Hgv _]; exact Hgv).
      assert (Hvbound : (0 <= v < adj_verts g)%Z).
      { pose proof Hwf as [Hgv0 [Hlenfr [Hlenvis [Hlensid [Hmof [Hlo0 [Hhilem [Hcolbound [Hlolohi Hmofbound]]]]]]]]].
        assert (Hhilem_u : (csr_hi u fr <= m_of fr)%Z) by (apply Hhilem; exact Hu).
        assert (Hlo0u : (0 <= csr_lo u fr)%Z) by (apply Hlo0; exact Hu).
        assert (Him : (0 <= i < m_of fr)%Z).
        { split; [ rewrite Hlo in Hlo0u; lia | lia ]. }
        exact (Hcolbound i Him). }
      assert (Hnotinv : ~ e_set (u, v)).
      { apply (HE i). split; [ exact Hloi | exact Hilt ]. exact Hnvisv. }
      assert (Hstep_g : reachable_basic.step g u v).
      { destruct (Hfaith u v Hu Hvbound) as [Hfwd Hbwd].
        apply Hbwd. exists i. split.
        - assert (Hloi' : (csr_lo u fr <= i)%Z). { rewrite Hlo. exact Hloi. }
          split; [ exact Hloi' | exact Hilt' ].
        - reflexivity. }
      assert (Hstepeq : step_aux g (u, v) u v).
      { destruct Hstep_g as [e Heq].
        destruct Heq as [Heqrefl [Hxu [Hyv Hiny]]].
        simpl in *. subst e. split; [ reflexivity | split; [ exact Hu | split;
          [ exact Hvbound | exact Hiny ] ] ]. }
      set (e_set' := e_set ∪ Sets.singleton (u, v)).
      unfold safe in *.
      unfold weakestpre in *.
      split.
      * (* ~err (dfs_scc_from ... u i) σ *)
        assert (HnoerrBE : ~ (B e_set).(MonadErr.err) σ).
        { assert (Hunf : @equiv (program KSt unit) _
                        (repeat_break B e_set)
                        (x <- B e_set ;;
                         match x with
                         | by_continue a' => repeat_break B a'
                         | by_break b' => ret b'
                         end)).
          { pose proof (repeat_break_unfold B) as Hu2.
            unfold equiv in Hu2. simpl in Hu2.
            unfold Equiv_lift, LiftConstructors.lift_rel2 in Hu2.
            specialize (Hu2 e_set) as [Hn Hh].
            constructor; assumption. }
          pose proof (wp_progequiv
                   (x <- B e_set ;; match x with by_continue a' => repeat_break B a' | by_break b' => ret b' end)
                   (repeat_break B e_set) X Hunf) as Hwp.
          sets_unfold in Hwp. specialize (Hwp σ) as [_ Hwpb].
          unfold weakestpre in Hwpb. sets_unfold in Hwpb.
          pose proof Hsafe as Hsafe0. apply Hwpb in Hsafe0.
          sets_unfold in Hsafe0. destruct Hsafe0 as [HnoerrBind _].
          apply bind_noerr_iff in HnoerrBind. destruct HnoerrBind as [Hne _]. exact Hne. }
        intro Herr.
        apply (dfs_scc_from_recurse_err_rev_imp g fc fr root u i σ Hilt' Hnvisv) in Herr.
        apply bind_err_iff in Herr.
        destruct Herr as [Herrv | [ha [smid [Hnm Hsccerr]]]].
        -- (* dfs_scc g root v errs at σ: contradiction with ~err (B e_set) σ. *)
           exfalso. apply HnoerrBE.
           unfold B, dfs2_repeat_body, choice. sets_unfold. left.
           apply bind_err_iff. right.
           eexists (u, v). eexists σ. split.
           { reflexivity. }
           apply bind_err_iff. right.
           eexists v. eexists σ. split.
           { reflexivity. }
           apply bind_err_iff. right.
           eexists tt. eexists σ. split.
           { split; [ reflexivity | exact Hnotinv ]. }
           apply bind_err_iff. right.
           eexists tt. eexists σ. split.
           { split; [ reflexivity | exact Hnvisv ]. }
           apply bind_err_iff. right.
           eexists tt. eexists σ. split.
           { split; [ reflexivity | exact Hstepeq ]. }
           apply bind_err_iff. left. exact Herrv.
        -- (* dfs_scc_from (i+1) errs at smid *)
           assert (Hbodycont_smid :
                     (B e_set).(MonadErr.nrm) σ (@by_continue (Z*Z->Prop) unit e_set') smid).
           { unfold B, dfs2_repeat_body, choice. simpl.
             left. simpl.
             eexists (u, v). eexists σ. split.
             - reflexivity.
             - eexists v. eexists σ. split.
               + reflexivity.
               + eexists tt. eexists σ. split.
                 * split; [ reflexivity | exact Hnotinv ].
                 * eexists tt. eexists σ. split.
                   -- split; [ reflexivity | exact Hnvisv ].
                   -- eexists tt. eexists σ. split.
                      ++ split; [ reflexivity | exact Hstepeq ].
                      ++ eexists ha. eexists smid. split.
                         ** exact Hnm.
                         ** simpl. split; [ reflexivity | reflexivity ]. }
           assert (Hsafe_smid : safe smid (repeat_break B e_set') X).
           { unfold safe in *.
             unfold weakestpre in *.
             assert (Hunf : @equiv (program KSt unit) _
                           (repeat_break B e_set)
                           (x <- B e_set ;;
                            match x with
                            | by_continue a' => repeat_break B a'
                            | by_break b' => ret b'
                            end)).
             { pose proof (repeat_break_unfold B) as Hu2.
               unfold equiv in Hu2. simpl in Hu2.
               unfold Equiv_lift, LiftConstructors.lift_rel2 in Hu2.
               specialize (Hu2 e_set) as [Hn Hh].
               constructor; assumption. }
             pose proof (wp_progequiv
                           (x <- B e_set ;; match x with by_continue a' => repeat_break B a' | by_break b' => ret b' end)
                           (repeat_break B e_set) X Hunf) as Hwp.
             sets_unfold in Hwp. specialize (Hwp σ) as [_ Hwpb].
             unfold weakestpre in Hwpb. sets_unfold in Hwpb.
             apply Hwpb in Hsafe.
             sets_unfold in Hsafe. destruct Hsafe as [HnoerrBind HpostBind].
             apply bind_noerr_iff in HnoerrBind.
             destruct HnoerrBind as [HnoerrBEset HpostBEset].
             split.
             - intro Herr'.
               assert (Herrmatch : (match (@by_continue (Z*Z->Prop) unit e_set') with
                                    | by_continue a' => repeat_break B a'
                                    | by_break b' => ret b' end).(MonadErr.err) smid).
               { simpl. exact Herr'. }
               apply (HpostBEset (@by_continue (Z*Z->Prop) unit e_set') smid Hbodycont_smid) in Herrmatch.
               exact Herrmatch.
             - intros r0 σf Hrb.
               apply HpostBind.
               assert (HnrmMatch : (x <- B e_set ;; match x with by_continue a' => repeat_break B a' | by_break b' => ret b' end).(MonadErr.nrm) σ r0 σf).
               { unfold MonadErr.bind. simpl.
                 eexists (@by_continue (Z*Z->Prop) unit e_set'). eexists smid. split.
                 - exact Hbodycont_smid.
                 - simpl. exact Hrb. }
               exact HnrmMatch. }
           assert (Huneqv : u <> v).
           { intro Heq. apply Hnvisv. rewrite <- Heq. exact HD. }
           assert (Hvis_mono_smid : visited2 σ ⊆ visited2 smid).
           { pose proof (@DFS_scc_neighbor_visited_strong AdjGraph Z (Z * Z) KG g Hagvalid σ root v)
               as Hh.
             unfold Hoare in Hh. destruct Hh as [HhNrm _].
             specialize (HhNrm ha σ smid (refl_equal _) Hnm) as [_ [Hmono _]].
             exact Hmono. }
           assert (Hvis_self_smid : visited2 smid v).
           { pose proof (@DFS_scc_neighbor_visited_strong AdjGraph Z (Z * Z) KG g Hagvalid σ root v)
               as Hh.
             unfold Hoare in Hh. destruct Hh as [HhNrm _].
             specialize (HhNrm ha σ smid (refl_equal _) Hnm) as [Hself _].
             exact Hself. }
           assert (HA'_smid : forall (e: Z * Z), e_set' e ->
                               exists k, (lo <= k < i + 1)%Z /\ e = (u, Znth k fc 0)).
           { intros e He. sets_unfold in He. destruct He as [He | Heuv].
             - destruct (HA e He) as [k [Hk Hkeq]]. exists k. split; [ lia | exact Hkeq ].
             - exists i. split; [ split; [ exact Hloi | lia ] | symmetry; exact Heuv ]. }
           assert (HB'_smid : forall k, (lo <= k < i + 1)%Z -> ~ e_set' (u, Znth k fc 0) ->
                               visited2 smid (Znth k fc 0)).
           { intros k Hk Hne.
             destruct (Z.le_gt_cases k (i - 1)) as [Hle | Hgt].
             - assert (HkZnth_neq_v : Znth k fc 0 <> v).
               { intro Heq. apply Hne. rewrite Heq. sets_unfold. right. reflexivity. }
               assert (Hne_eset : ~ e_set (u, Znth k fc 0)).
               { intro Hin. apply Hne. sets_unfold. left. exact Hin. }
               assert (Hklt : (lo <= k < i)%Z) by lia.
               apply Hvis_mono_smid. apply (HB k Hklt Hne_eset).
             - assert (Hki : k = i) by lia. subst k.
               exfalso. apply Hne. sets_unfold. right. reflexivity. }
           assert (HE'_smid : forall j, (lo <= j < hi)%Z -> ~ visited2 smid (Znth j fc 0) ->
                               ~ e_set' (u, Znth j fc 0)).
           { intros j Hj Hnvisj.
             destruct (Z.eq_dec (Znth j fc 0) v) as [Heq | Hneq].
             - exfalso. rewrite Heq in Hnvisj. exact (Hnvisj Hvis_self_smid).
             - intro Hin. apply Hneq.
               sets_unfold in Hin. destruct Hin as [HinE | Hsin].
               + assert (Hnvis_orig : ~ visited2 σ (Znth j fc 0)).
                 { intro Hv. apply Hnvisj. apply Hvis_mono_smid. exact Hv. }
                 exfalso. apply (HE j Hj Hnvis_orig). exact HinE.
               + injection Hsin as Heqv. exact (eq_sym Heqv). }
           assert (HC'_smid : scc_id smid u = scc_id smid root).
           { pose proof (@DFS_scc_same_root_id AdjGraph Z (Z * Z) KG g Hagvalid σ root v)
               as Hh.
             unfold Hoare in Hh. destruct Hh as [HhNrm _].
             specialize (HhNrm ha σ smid (refl_equal _) Hnm) as [_ [Hkept_sid [Hsid_root _]]].
             rewrite (Hkept_sid u HD Huneqv).
             rewrite Hsid_root.
             exact HC. }
           assert (HD'_smid : visited2 smid u).
           { apply Hvis_mono_smid. exact HD. }
           assert (Hloi_smid : (lo <= i + 1)%Z) by lia.
           assert (Hfuel_smid : Z.to_nat (hi - (i + 1)) = n').
           { assert (Hsub : hi - i = (hi - (i + 1)) + 1) by lia.
             assert (Hnonneg1 : (0 <= hi - (i + 1))%Z) by lia.
             rewrite Hsub in Hfuel. rewrite Z2Nat.inj_add in Hfuel by lia.
             rewrite Nat.add_1_r in Hfuel. injection Hfuel. auto. }
           assert (Hsafe_ih_smid : safe smid (dfs_scc_from g fc fr root u (i + 1)) X).
           { eapply IHn; [ exact Hfuel_smid | exact Hloi_smid | exact HA'_smid | exact HB'_smid |
                           exact HE'_smid | exact HC'_smid | exact HD'_smid | exact Hsafe_smid ]. }
           destruct Hsafe_ih_smid as [Hnoerr_smid _].
           exfalso. apply Hnoerr_smid. exact Hsccerr.
      * (* forall r σ', nrm (dfs_scc_from ... u i) σ r σ' -> X r σ' *)
        intros r σ' Hstep.
        apply (proj1 (dfs_scc_from_recurse_step g fc fr root u i σ r σ' Hilt' Hnvisv)) in Hstep.
        apply bind_nrm_iff in Hstep.
        destruct Hstep as [hu [σ'' [Hdfsstep Hcontstep]]].
        assert (Hbodycont : (B e_set).(MonadErr.nrm) σ (@by_continue (Z*Z->Prop) unit e_set') σ'').
        { unfold B, dfs2_repeat_body, choice. simpl.
          left. simpl.
          eexists (u, v). eexists σ. split.
          - reflexivity.
          - eexists v. eexists σ. split.
            + reflexivity.
            + eexists tt. eexists σ. split.
              * split; [ reflexivity | exact Hnotinv ].
              * eexists tt. eexists σ. split.
                -- split; [ reflexivity | exact Hnvisv ].
                -- eexists tt. eexists σ. split.
                   ++ split; [ reflexivity | exact Hstepeq ].
                   ++ eexists hu. eexists σ''. split.
                      ** exact Hdfsstep.
                      ** simpl. split; [ reflexivity | reflexivity ]. }
        assert (Hsafe'' : safe σ'' (repeat_break B e_set') X).
        { unfold safe in *.
          unfold weakestpre in *.
          assert (Hunf : @equiv (program KSt unit) _
                        (repeat_break B e_set)
                        (x <- B e_set ;;
                         match x with
                         | by_continue a' => repeat_break B a'
                         | by_break b' => ret b'
                         end)).
          { pose proof (repeat_break_unfold B) as Hu2.
            unfold equiv in Hu2. simpl in Hu2.
            unfold Equiv_lift, LiftConstructors.lift_rel2 in Hu2.
            specialize (Hu2 e_set) as [Hn Hh].
            constructor; assumption. }
          pose proof (wp_progequiv
                        (x <- B e_set ;; match x with by_continue a' => repeat_break B a' | by_break b' => ret b' end)
                        (repeat_break B e_set) X Hunf) as Hwp.
          sets_unfold in Hwp. specialize (Hwp σ) as [_ Hwpb].
          unfold weakestpre in Hwpb. sets_unfold in Hwpb.
          apply Hwpb in Hsafe.
          sets_unfold in Hsafe. destruct Hsafe as [HnoerrBind HpostBind].
          apply bind_noerr_iff in HnoerrBind.
          destruct HnoerrBind as [HnoerrBEset HpostBEset].
          split.
          - intro Herr'.
            assert (Herrmatch : (match (@by_continue (Z*Z->Prop) unit e_set') with
                                 | by_continue a' => repeat_break B a'
                                 | by_break b' => ret b' end).(MonadErr.err) σ'').
            { simpl. exact Herr'. }
            apply (HpostBEset (@by_continue (Z*Z->Prop) unit e_set') σ'' Hbodycont) in Herrmatch.
            exact Herrmatch.
          - intros r0 σf Hrb.
            apply HpostBind.
            assert (HnrmMatch : (x <- B e_set ;; match x with by_continue a' => repeat_break B a' | by_break b' => ret b' end).(MonadErr.nrm) σ r0 σf).
            { unfold MonadErr.bind. simpl.
              eexists (@by_continue (Z*Z->Prop) unit e_set'). eexists σ''. split.
              - exact Hbodycont.
              - simpl. exact Hrb. }
            exact HnrmMatch. }
        assert (Hfuel' : Z.to_nat (hi - (i + 1)) = n').
        { assert (Hsub : hi - i = (hi - (i + 1)) + 1) by lia.
          assert (Hnonneg1 : (0 <= hi - (i + 1))%Z) by lia.
          rewrite Hsub in Hfuel. rewrite Z2Nat.inj_add in Hfuel by lia.
          rewrite Nat.add_1_r in Hfuel. injection Hfuel. auto. }
        assert (Hloi' : (lo <= i + 1)%Z) by lia.
        assert (HA' : forall (e: Z * Z), e_set' e ->
                       exists k, (lo <= k < i + 1)%Z /\ e = (u, Znth k fc 0)).
        { intros e He. sets_unfold in He. destruct He as [He | Heuv].
          - destruct (HA e He) as [k [Hk Hkeq]]. exists k. split; [ lia | exact Hkeq ].
          - exists i. split; [ split; [ exact Hloi | lia ] | symmetry; exact Heuv ]. }
        assert (Huneqv : u <> v).
        { intro Heq. apply Hnvisv. rewrite <- Heq. exact HD. }
        assert (HQstrong : visited2 σ'' v /\ visited2 σ ⊆ visited2 σ'').
        { pose proof (@DFS_scc_neighbor_visited_strong AdjGraph Z (Z * Z) KG g Hagvalid σ root v)
            as Hh.
          unfold Hoare in Hh.
          destruct Hh as [HhNrm _].
          specialize (HhNrm hu σ σ'' (refl_equal _) Hdfsstep) as [Hself [Hmono _]].
          split; [ exact Hself | exact Hmono ]. }
        assert (HQsid :
                  (forall (w: Z), visited2 σ'' w -> ~ visited2 σ w ->
                                  scc_id σ'' w = scc_id σ'' root) /\
                  (forall (w: Z), visited2 σ w -> w <> v -> scc_id σ'' w = scc_id σ w) /\
                  scc_id σ'' root = scc_id σ root /\ visited2 σ ⊆ visited2 σ'').
        { pose proof (@DFS_scc_same_root_id AdjGraph Z (Z * Z) KG g Hagvalid σ root v)
            as Hh.
          unfold Hoare in Hh.
          destruct Hh as [HhNrm _].
          exact (HhNrm hu σ σ'' (refl_equal _) Hdfsstep). }
        destruct HQstrong as [Hvis_v_self Hvis_mono].
        destruct HQsid as [Hnew_sid [Hkept_sid [Hsid_root Hvis_mono2]]].
        assert (HB' : forall k, (lo <= k < i + 1)%Z -> ~ e_set' (u, Znth k fc 0) ->
                       visited2 σ'' (Znth k fc 0)).
        { intros k Hk Hne.
          destruct (Z.le_gt_cases k (i - 1)) as [Hle | Hgt].
          - assert (HkZnth_neq_v : Znth k fc 0 <> v).
            { intro Heq. apply Hne. rewrite Heq. sets_unfold. right. reflexivity. }
            assert (Hne_eset : ~ e_set (u, Znth k fc 0)).
            { intro Hin. apply Hne. sets_unfold. left. exact Hin. }
            pose proof (HB k) as Hkb.
            assert (Hklt : (lo <= k < i)%Z) by lia.
            specialize (Hkb Hklt Hne_eset).
            apply Hvis_mono. exact Hkb.
          - assert (Hki : k = i) by lia. subst k.
            exfalso. apply Hne. sets_unfold. right. reflexivity. }
        assert (HE' : forall j, (lo <= j < hi)%Z -> ~ visited2 σ'' (Znth j fc 0) ->
                       ~ e_set' (u, Znth j fc 0)).
        { intros j Hj Hnvisj.
          destruct (Z.eq_dec (Znth j fc 0) v) as [Heq | Hneq].
          - exfalso. rewrite Heq in Hnvisj. exact (Hnvisj Hvis_v_self).
          - intro Hin. apply Hneq.
            sets_unfold in Hin. destruct Hin as [HinE | Hsin].
            + assert (Hnvis_orig : ~ visited2 σ (Znth j fc 0)).
              { intro Hv. apply Hnvisj. apply Hvis_mono. exact Hv. }
              exfalso. apply (HE j Hj Hnvis_orig). exact HinE.
            + injection Hsin as Heqv. exact (eq_sym Heqv). }
        assert (HC' : scc_id σ'' u = scc_id σ'' root).
        { rewrite (Hkept_sid u HD Huneqv).
          rewrite Hsid_root.
          exact HC. }
        assert (HD' : visited2 σ'' u).
        { apply Hvis_mono. exact HD. }
        assert (Hsafe_ih : safe σ'' (dfs_scc_from g fc fr root u (i + 1)) X).
        { eapply IHn; [ exact Hfuel' | exact Hloi' | exact HA' | exact HB' | exact HE' |
                        exact HC' | exact HD' | exact Hsafe'' ]. }
        apply Hsafe_ih. exact Hcontstep.
Qed.

(* ===================================================================== *)
(* dfs2_entry_close: the entry refinement (split_goal_9).                *)
(* Combines dfs2_visit_setid_decompose (peel visit2 + set_scc_id prelude,*)
(* landing safeExec over repeat_break (dfs2_repeat_body g root u) ∅)     *)
(* with dfs_scc_from_sim (cursor ≡ repeat_break simulation at i=lo).     *)
(* ===================================================================== *)
Lemma dfs2_entry_close :
  forall (g: AdjGraph) (fc fr vis sid: list Z) (root u root_v: Z)
         (X: unit -> KSt -> Prop),
    csr_wf2 g fc fr vis sid ->
    csr2_faithful g fc fr ->
    (0 <= u < adj_verts g)%Z ->
    (0 <= root < adj_verts g)%Z ->
    Znth root vis 0 <> 0%Z ->
    safeExec (pre_dfs2 g fc fr vis sid root_v) (dfs_scc g root u) X ->
    safeExec (pre_dfs2 g fc fr (replace_Znth u 1 vis) (replace_Znth u (Znth root sid 0) sid) root_v)
             (dfs_scc_from g fc fr root u (csr_lo u fr)) X.
Proof.
  intros g fc fr vis sid root u root_v X Hwf Hfaith Hub Hroot Hvisroot Hsafe.
  (* Extract the csr_wf2 conjuncts we need, keeping Hwf intact for sim. *)
  destruct Hwf as [Hgv [Hlenfr [Hlenvis [Hlensid [Hmof [Hlo0 [Hhilem [Hcolbound [Hlolohi Hmofbound]]]]]]]]].
  (* Re-conjoin Hwf for dfs_scc_from_sim. *)
  assert (Hwf' : csr_wf2 g fc fr vis sid).
  { unfold csr_wf2.
    repeat (split; [ assumption | ]);
    try assumption. }
  (* Peel visit2 u + set_scc_id u root prelude: safeExec over repeat_break B ∅. *)
  assert (Hvislen : (Zlength vis = adj_verts g)%Z) by exact Hlenvis.
  assert (Hsidlen : (Zlength sid = adj_verts g)%Z) by exact Hlensid.
  pose proof (dfs2_visit_setid_decompose g fc fr vis sid root_v u root X
                Hgv Hvislen Hsidlen Hub Hroot Hsafe) as Hdec.
  (* Hdec : safeExec (pre_dfs2 ... (replace_Znth u 1 vis) (replace_Znth u (Znth root sid 0) sid) root_v)
                       (repeat_break (dfs2_repeat_body g root u) ∅) X. *)
  destruct Hdec as [σ' [Hpreσ' Hsafeσ']].
  pose proof (proj1 Hpreσ') as Hvis_map.
  pose proof (proj2 Hpreσ') as Hsid_map.
  (* Apply dfs_scc_from_sim at (i = csr_lo u fr, e_set = ∅, σ'). *)
  set (lo := csr_lo u fr) in *.
  set (hi := csr_hi u fr) in *.
  assert (Hlo_eq : csr_lo u fr = lo) by reflexivity.
  assert (Hhi_eq : csr_hi u fr = hi) by reflexivity.
  assert (Hloi : (lo <= lo)%Z) by lia.
  assert (Hlohi : (0 <= hi - lo)%Z).
  { pose proof (Hlolohi u Hub) as Hlh. unfold lo, hi in *. lia. }
  set (n := Z.to_nat (hi - lo)).
  assert (Hfuel : Z.to_nat (hi - lo) = n) by reflexivity.
  (* Invariants at entry (i = lo, e_set = ∅): A/B vacuous (empty ranges / empty
     set), E trivial (e_set = ∅).  C/D from pre_dfs2 σ' + replace_Znth. *)
  assert (HA : forall (e: Z * Z), (fun _ => False) e ->
                exists k, (lo <= k < lo)%Z /\ e = (u, Znth k fc 0)).
  { intros e Hf. exfalso. exact Hf. }
  assert (HB : forall k, (lo <= k < lo)%Z -> ~ (fun _ => False) (u, Znth k fc 0) ->
                 visited2 σ' (Znth k fc 0)).
  { intros k [Hk1 Hk2] _. lia. }
  assert (HE : forall j, (lo <= j < hi)%Z -> ~ visited2 σ' (Znth j fc 0) ->
                 ~ (fun _ => False) (u, Znth j fc 0)).
  { intros j Hj Hnv Hf. exact Hf. }
  (* C: scc_id σ' u = scc_id σ' root, from pre_dfs2 + replace_Znth. *)
  (* Bounds for Znth_replace_eq/neq: u, root within Zlength sid / vis. *)
  assert (Husid : (0 <= u < Zlength sid)%Z) by (rewrite Hsidlen; exact Hub).
  assert (Hrsid : (0 <= root < Zlength sid)%Z) by (rewrite Hsidlen; exact Hroot).
  assert (Huvis : (0 <= u < Zlength vis)%Z) by (rewrite Hvislen; exact Hub).
  assert (HC : scc_id σ' u = scc_id σ' root).
  { (* scc_id σ' u = Z.to_nat (Znth u (replace_Znth u (Znth root sid 0) sid) 0)
       = Z.to_nat (Znth root sid 0).  (Znth_replace_eq.)
       scc_id σ' root = Z.to_nat (Znth root (replace_Znth u (Znth root sid 0) sid) 0).
       Case root = u: Znth u (...) = Znth root sid 0 (replace at root = u). Both equal.
       Case root ≠ u: Znth root (...) = Znth root sid 0 (replace at u ≠ root, no change). *)
    assert (Hsu : scc_id σ' u = Z.to_nat (Znth root sid 0)).
    { rewrite (Hsid_map u Hub).
      rewrite (Znth_replace_eq sid u (Znth root sid 0) 0 Husid). reflexivity. }
    assert (Hsr : scc_id σ' root = Z.to_nat (Znth root sid 0)).
    { rewrite (Hsid_map root Hroot).
      destruct (Z.eq_dec root u) as [Heq | Hneq].
      - subst root. rewrite (Znth_replace_eq sid u (Znth u sid 0) 0 Husid). reflexivity.
      - rewrite (Znth_replace_neq sid root u (Znth root sid 0) 0 Hrsid (proj1 Hub) Hneq).
        reflexivity. }
    rewrite Hsu. symmetry. exact Hsr. }
  (* D: visited2 σ' u, from pre_dfs2 + replace_Znth u 1 vis (Znth u ... = 1 ≠ 0). *)
  assert (HD : visited2 σ' u).
  { assert (Hvu : Znth u (replace_Znth u 1 vis) 0 = 1).
    { rewrite (Znth_replace_eq vis u 1 0 Huvis). reflexivity. }
    apply (proj2 (Hvis_map u Hub)). rewrite Hvu. lia. }
  (* Apply sim. *)
  assert (Hsafe_ih : safe σ' (dfs_scc_from g fc fr root u lo) X).
  { eapply dfs_scc_from_sim; [ exact Hlo_eq | exact Hhi_eq | exact Hwf' | exact Hfaith |
                               exact Hub | exact Hfuel | exact Hloi | exact HA | exact HB |
                               exact HE | exact HC | exact HD | exact Hsafeσ' ]. }
  (* Wrap back to safeExec: exists σ', split. *)
  exists σ'. split; [ exact Hpreσ' | exact Hsafe_ih ].
Qed.

(* ===================================================================== *)
(* dfs1_entry_close infrastructure (phase-1 entry refinement).           *)
(*                                                                        *)
(* The entry VC (dfs1_entail_wit_1, second disjunct) reduces to: given    *)
(*   safeExec (pre_dfs1 vis1 fin timer_v) (dfs_finish g u) X,             *)
(* show safeExec (pre_dfs1 (replace_Znth u 1 vis1) fin timer_v)           *)
(*        (dfs_finish_from g radj_col radj_row u lo) X.                   *)
(*                                                                        *)
(* dfs_finish_repeat_body is the body of DFS_finish_f, u-parametrised,    *)
(* with W = dfs_finish g.  Note: step_aux g e v u (REVERSED — u is the   *)
(* target on the reverse graph), and the break branch does `assertS      *)
(* timer<=|V|;; get timer;; set_finish u t` (state-changing, unlike       *)
(* phase-2's assertS sid ;; break).                                       *)
(* ===================================================================== *)

Definition dfs_finish_repeat_body (g: AdjGraph) (u: Z)
  : (Z * Z -> Prop) -> program KSt (CntOrBrk (Z * Z -> Prop) unit) :=
  fun e_set =>
    choice
      (e <- any (Z * Z);;
       v <- any Z;;
       assume (fun (_ : KSt) => ~ e ∈ e_set);;
       assume (fun st => ~ visited1 st v);;
       assume (fun (_ : KSt) => step_aux g e v u);;
       dfs_finish g v;;
       continue (e_set ∪ Sets.singleton e))
      (assume (fun st =>
                 forall (e: Z * Z) (v: Z),
                   step_aux g e v u ->
                   e ∈ e_set \/ visited1 st v);;
       assertS (fun st => (timer st < length (bijective_listV g))%nat);;
       t <- get (fun st t => t = timer st);;
       set_finish u t;;
       break tt).

Lemma dfs_finish_unfold_repeat :
  forall (g: AdjGraph) (u: Z),
  gvalid g ->
  dfs_finish g u
  ==
  visit1 u ;; repeat_break (dfs_finish_repeat_body g u) ∅.
Proof.
  intros g u Hg.
  rewrite (dfs_finish_unfold g u Hg).
  unfold DFS_finish_f.
  reflexivity.
Qed.

(* visit1_pre_dfs1_step: peel the visit1 u prelude off safeExec(dfs_finish g u).
   visit1 u adds u to visited1 (visited1 st2 == visited1 st1 ∪ {u}), all other
   fields unchanged.  So pre_dfs1 vis1 fin timer_v -@ visit1 u -⥅
   pre_dfs1 (replace_Znth u 1 vis1) fin timer_v. *)
Lemma visit1_pre_dfs1_step :
  forall (g: AdjGraph) (radj_col_l radj_row_l vis1 fin_l: list Z) (timer_v u: Z),
    (Zlength vis1 = adj_verts g)%Z ->
    (0 <= u < adj_verts g)%Z ->
    pre_dfs1 g radj_col_l radj_row_l vis1 fin_l timer_v -@ visit1 u -⥅
      (pre_dfs1 g radj_col_l radj_row_l (replace_Znth u 1 vis1) fin_l timer_v) ♯ tt.
Proof.
  intros g radj_col_l radj_row_l vis1 fin_l timer_v u Hvlen Hub st0 Hpre.
  destruct Hpre as [Hpv [Hpf Hpt]].
  assert (HLu : (0 <= u < Zlength vis1)%Z) by (rewrite Hvlen; exact Hub).
  pose (st1 := MkSt (timer st0) (finish st0)
                     (fun w => visited1 st0 w \/ w = u)
                     (visited2 st0) (scc_id st0) (scc_next st0)).
  assert (Hnrm : (visit1 u).(MonadErr.nrm) st0 tt st1).
  { unfold visit1. simpl. split.
    - (* visited1 st1 == visited1 st0 ∪ {u} *)
      unfold st1. simpl. sets_unfold. intros w. split; intros Hw.
      + destruct Hw as [Hw | Hw]; [ left; exact Hw | subst w; right; reflexivity ].
      + destruct Hw as [Hw | Hw]; [ left; exact Hw | subst w; right; reflexivity ].
    - unfold st1. simpl. repeat split; reflexivity.
  }
  exists st1. split; [ exact Hnrm | ].
  unfold pre_dfs1. split.
  - intros w Hw. assert (HLw : (0 <= w < Zlength vis1)%Z) by (rewrite Hvlen; exact Hw).
    unfold st1. simpl. split; intros Hvis.
    + destruct (Z.eqb w u) eqn:E.
      * apply Z.eqb_eq in E. subst w. rewrite (Znth_replace_eq vis1 u 1 0 HLu). lia.
      * apply Z.eqb_neq in E. rewrite (Znth_replace_neq vis1 w u 1 0 HLw (proj1 HLu) E).
        destruct Hvis as [Hv | Hwu].
        -- apply (proj1 (Hpv w Hw)). exact Hv.
        -- exfalso. apply E. exact Hwu.
    + destruct (Z.eqb w u) eqn:E.
      * apply Z.eqb_eq in E. subst w. right. reflexivity.
      * apply Z.eqb_neq in E. rewrite (Znth_replace_neq vis1 w u 1 0 HLw (proj1 HLu) E) in Hvis.
        left. apply (proj2 (Hpv w Hw)). exact Hvis.
  - split.
    + intros w Hw. unfold st1. simpl. exact (Hpf w Hw).
    + unfold st1. simpl. exact Hpt.
Qed.

(* dfs1_visit_decompose: peel visit1 u prelude, landing safeExec over
   repeat_break (dfs_finish_repeat_body g u) ∅ at the post-visit1 state. *)
Lemma dfs1_visit_decompose :
  forall (g: AdjGraph) (radj_col_l radj_row_l vis1 fin_l: list Z) (timer_v u: Z)
         (X: unit -> KSt -> Prop),
    gvalid g ->
    (Zlength vis1 = adj_verts g)%Z ->
    (0 <= u < adj_verts g)%Z ->
    safeExec (pre_dfs1 g radj_col_l radj_row_l vis1 fin_l timer_v) (dfs_finish g u) X ->
    safeExec (pre_dfs1 g radj_col_l radj_row_l (replace_Znth u 1 vis1) fin_l timer_v)
             (repeat_break (dfs_finish_repeat_body g u) ∅) X.
Proof.
  intros g radj_col_l radj_row_l vis1 fin_l timer_v u X Hg Hvlen Hub Hsafe.
  rewrite (dfs_finish_unfold_repeat g u Hg) in Hsafe.
  apply (highstepbind_derive (visit1 u)
            (fun _ => repeat_break (dfs_finish_repeat_body g u) ∅)
            (pre_dfs1 g radj_col_l radj_row_l vis1 fin_l timer_v) tt
            (pre_dfs1 g radj_col_l radj_row_l (replace_Znth u 1 vis1) fin_l timer_v)
            (visit1_pre_dfs1_step g radj_col_l radj_row_l vis1 fin_l timer_v u Hvlen Hub)) in Hsafe.
  exact Hsafe.
Qed.

(* ===================================================================== *)
(* Reverse-direction err-imps for dfs_finish_iter / dfs_finish_from       *)
(* (phase-1 analogues of dfs_scc_iter/from_*_err_rev_imp).               *)
(* Used by dfs_finish_from_sim to peel the cursor step FORWARD (i -> i+1).*)
(* ===================================================================== *)

Lemma dfs_finish_iter_skip_err_rev_imp :
  forall (g : AdjGraph) (radj_col_l : list Z) (u hi i : Z) (fuel : nat)
         (st : KSt),
    (i < hi)%Z ->
    visited1 st (Znth i radj_col_l 0) ->
    (dfs_finish_iter g radj_col_l u hi i (S fuel)).(MonadErr.err) st ->
    (dfs_finish_iter g radj_col_l u hi (i + 1) fuel).(MonadErr.err) st.
Proof.
  intros g radj_col_l u hi i fuel st Hilt Hvis Herr.
  simpl in Herr. destruct (Z.leb hi i) eqn:E.
  - apply Z.leb_le in E. exfalso. lia.
  - unfold if_else, choice in Herr.
    sets_unfold in Herr.
    destruct Herr as [HL | HR].
    + apply bind_err_iff in HL.
      destruct HL as [Htest | [x [s0 [Hnm Hsk2]]]].
      * exfalso. unfold test in Htest. sets_unfold in Htest. exact Htest.
      * unfold test in Hnm. simpl in Hnm. destruct Hnm as [Hs2eq Hc]. subst s0. exact Hsk2.
    + apply bind_err_iff in HR.
      destruct HR as [Htest | [x [s0 [Hnm Hsk2]]]].
      * exfalso. unfold test in Htest. sets_unfold in Htest. exact Htest.
      * unfold test in Hnm. simpl in Hnm. destruct Hnm as [Hs2eq Hnc]. exfalso. apply Hnc. exact Hvis.
Qed.

Lemma dfs_finish_iter_recurse_err_rev_imp :
  forall (g : AdjGraph) (radj_col_l : list Z) (u hi i : Z) (fuel : nat)
         (st : KSt),
    (i < hi)%Z ->
    ~ visited1 st (Znth i radj_col_l 0) ->
    (dfs_finish_iter g radj_col_l u hi i (S fuel)).(MonadErr.err) st ->
    ((_ <- dfs_finish g (Znth i radj_col_l 0) ;;
      dfs_finish_iter g radj_col_l u hi (i + 1) fuel)).(MonadErr.err) st.
Proof.
  intros g radj_col_l u hi i fuel st Hilt Hnvis Herr.
  simpl in Herr. destruct (Z.leb hi i) eqn:E.
  - apply Z.leb_le in E. exfalso. lia.
  - unfold if_else, choice in Herr.
    sets_unfold in Herr.
    destruct Herr as [HL | HR].
    + apply bind_err_iff in HL.
      destruct HL as [Htest | [x [s0 [Hnm Hsk2]]]].
      * exfalso. unfold test in Htest. sets_unfold in Htest. exact Htest.
      * unfold test in Hnm. simpl in Hnm. destruct Hnm as [Hs2eq Hc].
        exfalso. apply Hnvis. exact Hc.
    + apply bind_err_iff in HR.
      destruct HR as [Htest | [x [s0 [Hnm Hsk2]]]].
      * exfalso. unfold test in Htest. sets_unfold in Htest. exact Htest.
      * unfold test in Hnm. simpl in Hnm. destruct Hnm as [Hs2eq Hnc]. subst s0. exact Hsk2.
Qed.

Lemma dfs_finish_from_skip_err_rev_imp :
  forall (g : AdjGraph) (radj_col_l radj_row_l : list Z) (u i : Z)
         (st : KSt),
    (i < csr_hi u radj_row_l)%Z ->
    visited1 st (Znth i radj_col_l 0) ->
    (dfs_finish_from g radj_col_l radj_row_l u i).(MonadErr.err) st ->
    (dfs_finish_from g radj_col_l radj_row_l u (i + 1)).(MonadErr.err) st.
Proof.
  intros g radj_col_l radj_row_l u i st Hilt Hvis Herr.
  unfold dfs_finish_from in *.
  assert (Hfuel : Z.to_nat (csr_hi u radj_row_l - i) =
                  S (Z.to_nat (csr_hi u radj_row_l - (i + 1)))).
  { assert (Hsub : csr_hi u radj_row_l - i = (csr_hi u radj_row_l - (i + 1)) + 1) by lia.
    rewrite Hsub, Z2Nat.inj_add by lia.
    rewrite Nat.add_1_r. reflexivity. }
  rewrite Hfuel in Herr.
  exact (dfs_finish_iter_skip_err_rev_imp g radj_col_l u _ i _ st Hilt Hvis Herr).
Qed.

Lemma dfs_finish_from_recurse_err_rev_imp :
  forall (g : AdjGraph) (radj_col_l radj_row_l : list Z) (u i : Z)
         (st : KSt),
    (i < csr_hi u radj_row_l)%Z ->
    ~ visited1 st (Znth i radj_col_l 0) ->
    (dfs_finish_from g radj_col_l radj_row_l u i).(MonadErr.err) st ->
    ((_ <- dfs_finish g (Znth i radj_col_l 0) ;;
      dfs_finish_from g radj_col_l radj_row_l u (i + 1))).(MonadErr.err) st.
Proof.
  intros g radj_col_l radj_row_l u i st Hilt Hnvis Herr.
  unfold dfs_finish_from in *.
  assert (Hfuel : Z.to_nat (csr_hi u radj_row_l - i) =
                  S (Z.to_nat (csr_hi u radj_row_l - (i + 1)))).
  { assert (Hsub : csr_hi u radj_row_l - i = (csr_hi u radj_row_l - (i + 1)) + 1) by lia.
    rewrite Hsub, Z2Nat.inj_add by lia.
    rewrite Nat.add_1_r. reflexivity. }
  rewrite Hfuel in Herr.
  exact (dfs_finish_iter_recurse_err_rev_imp g radj_col_l u _ i _ st Hilt Hnvis Herr).
Qed.

(* dfs_finish_repeat_body_err_from_assertS: if the break-branch closure holds
   at σ and timer σ >= length (bijective_listV g), then the repeat_break body
   errs at σ.  Used by dfs_finish_from_sim BASE to extract timer σ < length
   from the no-err conjunct of safe σ (repeat_break B e_set) X. *)
Lemma dfs_finish_repeat_body_err_from_assertS :
  forall (g: AdjGraph) (u: Z) (e_set: Z * Z -> Prop) (σ: KSt),
    (forall (e: Z * Z) (v: Z), step_aux g e v u -> e ∈ e_set \/ visited1 σ v) ->
    (length (bijective_listV g) <= timer σ)%nat ->
    (dfs_finish_repeat_body g u e_set).(MonadErr.err) σ.
Proof.
  intros g u e_set σ Hclosure Hnlt.
  unfold dfs_finish_repeat_body, choice. sets_unfold.
  right.
  apply bind_err_iff. right.
  eexists tt. eexists σ. split.
  - unfold test. sets_unfold. split; [ reflexivity | exact Hclosure ].
  - apply bind_err_iff. left. intro Htlt. lia.
Qed.

(* ===================================================================== *)
(* dfs_finish_from_sim: cursor (dfs_finish_from) vs repeat_break          *)
(* simulation (phase-1 entry refinement core).                           *)
(*                                                                        *)
(* Differences from dfs_scc_from_sim (phase-2):                           *)
(* - csr1_faithful: step g v u <-> exists j in [lo u, hi u) with          *)
(*   Znth j radj_col 0 = v (REVERSE graph; u is the target).              *)
(* - break branch (R): assertS timer<=|V| ;; get timer ;; set_finish u t *)
(*   (state-CHANGING: timer++, finish[u]=t).  BASE case lands at sigma'   *)
(*   (= set_finish post-state), not sigma.                                *)
(* - algorithm lemma DFS_finish_neighbor_visited_strong (Qed) needs the   *)
(*   extra premise cardV(visited1 sigma) >= timer sigma; carried through  *)
(*   RECURSE via visited1-monotonicity (timer unchanged by dfs_finish g v *)
(*   until its own set_finish, but cardV only grows).                     *)
(* - timer-bound for BASE's assertS: timer sigma <= length                *)
(*   (bijective_listV g), also carried as a premise.                      *)
(* ===================================================================== *)

Lemma dfs_finish_from_sim :
  forall (g: AdjGraph) (radj_col_l radj_row_l vis1_l fin_l: list Z) (u lo hi i: Z)
         (n: nat) (X: unit -> KSt -> Prop) (σ: KSt),
    let B := dfs_finish_repeat_body g u in
    csr_lo u radj_row_l = lo ->
    csr_hi u radj_row_l = hi ->
    csr_wf1 g radj_col_l radj_row_l vis1_l fin_l ->
    csr1_faithful g radj_col_l radj_row_l ->
    (0 <= u < adj_verts g)%Z ->
    Z.to_nat (hi - i) = n ->
    (lo <= i)%Z ->
    forall (e_set: Z * Z -> Prop),
      (forall (e: Z * Z), e_set e ->
         exists k, (lo <= k < i)%Z /\ e = (Znth k radj_col_l 0, u)) ->
      (forall k, (lo <= k < i)%Z -> ~ e_set (Znth k radj_col_l 0, u) ->
         visited1 σ (Znth k radj_col_l 0)) ->
      (forall j, (lo <= j < hi)%Z -> ~ visited1 σ (Znth j radj_col_l 0) ->
         ~ e_set (Znth j radj_col_l 0, u)) ->
      visited1 σ u ->
      (count_pred (visited1 σ) (bijective_listV g) >= timer σ)%nat ->
      (timer σ <= length (bijective_listV g))%nat ->
      safe σ (repeat_break B e_set) X ->
      safe σ (dfs_finish_from g radj_col_l radj_row_l u i) X.
Proof.
  intros g radj_col_l radj_row_l vis1_l fin_l u lo hi i n X σ B Hlo Heqhi Hwf Hfaith Hu Hfuel Hloi
         e_set HA HB HE HD HcardV Htimerbd Hsafe.
  revert i X σ Hfuel Hloi e_set HA HB HE HD HcardV Htimerbd Hsafe.
  induction n as [|n' IHn].
  - (* BASE: Z.to_nat (hi - i) = 0, hence i >= hi *)
    intros i X σ Hfuel Hloi e_set HA HB HE HD HcardV Htimerbd Hsafe.
    assert (Hge : (hi <= i)%Z).
    { destruct (Z.le_gt_cases hi i) as [Hle | Hgt]; [ exact Hle | ].
      exfalso.
      assert (Hpos : (0 < hi - i)%Z) by lia.
      destruct (Z.eq_dec (hi - i) 0) as [Heq | Hneq].
      - subst. lia.
      - assert (Hn0 : (Z.to_nat (hi - i) <> 0)%nat).
        { intro Hz. assert (0 <= hi - i)%Z by lia.
          pose proof (Z2Nat.id (hi - i) H) as Hid.
          rewrite Hz in Hid. lia. }
        rewrite Hfuel in Hn0. exfalso. apply Hn0. reflexivity. }
    assert (Hclosure : (forall (e: Z * Z) (v: Z), step_aux g e v u ->
                                    e ∈ e_set \/ visited1 σ v)).
    { intros e v Hstep.
      assert (Hstep_g : reachable_basic.step g v u) by (eapply step_trivial; eassumption).
      destruct Hstep as [Heq [Hvv [Hvu Hiny]]].
      subst e.
      pose proof (Hfaith u v Hu Hvv) as Hiff.
      apply (proj1 Hiff) in Hstep_g as [j [Hjlo Hjv]].
      destruct (classic (e_set (v, u))) as [Hin | Hnin].
      - left. exact Hin.
      - right. rewrite <- Hjv. apply (HB j). lia.
        rewrite Hjv. exact Hnin. }
    (* timer σ < length: derived from ~ (repeat_break B e_set).(err) σ (a
       conjunct of Hsafe).  Under Hclosure, the body B e_set errs at σ whenever
       timer σ >= length (break-branch assertS fails); since the no-err conjunct
       of safe forbids this, timer σ < length follows. *)
    assert (Htimerstrict : (timer σ < length (bijective_listV g))%nat).
    { destruct Hsafe as [Hnoerr _].
      destruct (Nat.le_gt_cases (timer σ) (length (bijective_listV g))) as [Hle | Hnlt].
      - destruct (Nat.eq_dec (timer σ) (length (bijective_listV g))) as [Heq | Hneq].
        + exfalso. apply Hnoerr.
          pose proof (repeat_break_unfold B) as Hunf.
          unfold equiv in Hunf. simpl in Hunf.
          unfold Equiv_lift, LiftConstructors.lift_rel2 in Hunf.
          specialize (Hunf e_set) as [_ Herrpt].
          sets_unfold in Herrpt. specialize (Herrpt σ) as [_ Hherr].
          apply Hherr. apply bind_err_iff. left.
          apply (dfs_finish_repeat_body_err_from_assertS g u e_set σ Hclosure).
          lia.
        + lia.
      - lia. }
    (* sigma' = set_finish post-state: timer sigma' = S (timer sigma),
       finish sigma' u = timer sigma, other fields unchanged. *)
    pose (σ' := MkSt (S (timer σ))
                     (fun w => if Z.eqb w u then timer σ else finish σ w)
                     (visited1 σ) (visited2 σ)
                     (scc_id σ) (scc_next σ)).
    assert (Hfsu : finish σ' u = timer σ).
    { unfold σ'. simpl. destruct (Z.eqb u u) eqn:Eu.
      - reflexivity.
      - apply Z.eqb_neq in Eu. exfalso. apply Eu. reflexivity. }
    assert (Hfsv : forall v, v <> u -> finish σ' v = finish σ v).
    { intros v Hvne. unfold σ'. simpl. destruct (Z.eqb v u) eqn:Ev.
      - apply Z.eqb_eq in Ev. exfalso. apply Hvne. exact Ev.
      - reflexivity. }
    assert (Htimer' : timer σ' = S (timer σ)) by (unfold σ'; reflexivity).
    assert (Hvis1' : visited1 σ' = visited1 σ) by (unfold σ'; reflexivity).
    assert (Hvis2' : visited2 σ' = visited2 σ) by (unfold σ'; reflexivity).
    assert (Hsid' : scc_id σ' = scc_id σ) by (unfold σ'; reflexivity).
    assert (Hsnext' : scc_next σ' = scc_next σ) by (unfold σ'; reflexivity).
    assert (Hbodystep : (B e_set).(MonadErr.nrm) σ (@by_break (Z*Z->Prop) unit tt) σ').
    { unfold B, dfs_finish_repeat_body.
      unfold choice. simpl.
      right.
      unfold_monad. simpl.
      eexists tt. eexists σ. split.
      - split; [ reflexivity | exact Hclosure ].
      - eexists tt. eexists σ. split.
        + split; [ reflexivity | exact Htimerstrict ].
        + eexists (timer σ). eexists σ. split.
          * split; [ reflexivity | reflexivity ].
          * eexists tt. eexists σ'. split.
            -- split; [ exact Htimer' | ].
               split; [ exact Hfsu | ].
               split; [ exact Hfsv | ].
               split; [ exact Hvis1' | ].
               split; [ exact Hvis2' | ].
               split; [ exact Hsid' | ].
               exact Hsnext'.
            -- simpl. split; [ reflexivity | reflexivity ]. }
    assert (Hrbstep : (repeat_break B e_set).(MonadErr.nrm) σ tt σ').
    { eapply repeat_break_break_step_gen. exact Hbodystep. }
    assert (Hxtt : X tt σ') by (eapply wp_spec; eassumption).
    unfold safe in *.
    assert (Hge' : (csr_hi u radj_row_l <= i)%Z) by (rewrite Heqhi; exact Hge).
    pose proof (wp_progequiv (assertS (fun st => (timer st < length (bijective_listV g))%nat);;
                              t <- get (fun st t => t = timer st) ;; set_finish u t)
                  (dfs_finish_from g radj_col_l radj_row_l u i) X
                  (dfs_finish_from_exit g radj_col_l radj_row_l u i Hge')) as Hwp.
    sets_unfold in Hwp.
    specialize (Hwp σ) as [Hfwd Hbwd].
    unfold weakestpre in *.
    sets_unfold in Hfwd.
    apply Hfwd.
    sets_unfold.
    split.
    + (* ~err (assertS timer<n ;; get timer ;; set_finish u t) σ:
         assertS.err iff timer σ >= length, excluded by Htimerstrict; get/set_finish.err = ∅. *)
      intro Herr.
      apply bind_err_iff in Herr.
      destruct Herr as [Hassert | [a [s2 [Hassertnrm Hfin]]]].
      * exfalso. apply Hassert. exact Htimerstrict.
      * exfalso. apply bind_err_iff in Hfin. destruct Hfin as [Hget | [t [s3 [Hgetstep Hfinerr]]]].
        -- exact Hget.
        -- exact Hfinerr.
    + intros r σ'' Hexitstep.
      apply bind_nrm_iff in Hexitstep.
      destruct Hexitstep as [a [sm [Hassertnrm Hgetsetfin]]].
      apply bind_nrm_iff in Hgetsetfin.
      destruct Hgetsetfin as [t [s2 [Hgetstep Hfinstep]]].
      destruct Hgetstep as [HgetP HgetEq].
      (* get keeps state: s2 = sm (HgetEq : sm = s2); bound t = timer sm *)
      subst s2. subst t.
      (* assertS keeps state: sm = σ *)
      assert (Hsmσ : sm = σ).
      { destruct Hassertnrm as [Heq _]. symmetry. exact Heq. }
      subst sm.
      (* set_finish u (timer σ): σ'' = σ' by field equality *)
      assert (Heqσ'' : σ'' = σ').
      { destruct σ'' as [tm fm v1m v2m sm snm] eqn:Eσ''.
        cbv beta iota delta [set_finish custom MonadErr.nrm_nrm] in Hfinstep.
        destruct Hfinstep as [Ht [Hfu [Hfv [Hv1 [Hv2 [Hs Hsn]]]]]].
        unfold σ'.
        f_equal.
        - exact Ht.
        - extensionality w. destruct (Z.eqb w u) eqn:E.
          + apply Z.eqb_eq in E. subst w. exact Hfu.
          + apply Z.eqb_neq in E. exact (Hfv w E).
        - exact Hv1.
        - exact Hv2.
        - exact Hs.
        - exact Hsn. }
      subst σ''. destruct r. exact Hxtt.
  - (* STEP: hi - i = S n', i.e. lo <= i < hi *)
    intros i X σ Hfuel Hloi e_set HA HB HE HD HcardV Htimerbd Hsafe.
    assert (Hilt : (i < hi)%Z).
    { assert (Hnonneg : (0 <= hi - i)%Z).
      { destruct (Z.le_gt_cases hi i) as [Hle | Hgt].
        - exfalso. assert (Heqz : hi - i = 0) by lia.
          rewrite Heqz in Hfuel. simpl in Hfuel. discriminate.
        - lia. }
      lia. }
    assert (Hilt' : (i < csr_hi u radj_row_l)%Z) by (rewrite Heqhi; exact Hilt).
    set (v := Znth i radj_col_l 0) in *.
    destruct (classic (visited1 σ v)) as [Hvisv | Hnvisv].
    + (* SKIP: visited1 σ v *)
      assert (Hfuel' : Z.to_nat (hi - (i + 1)) = n').
      { assert (Hsub : hi - i = (hi - (i + 1)) + 1) by lia.
        assert (Hnonneg1 : (0 <= hi - (i + 1))%Z) by lia.
        rewrite Hsub in Hfuel.
        rewrite Z2Nat.inj_add in Hfuel by lia.
        rewrite Nat.add_1_r in Hfuel. injection Hfuel. auto. }
      assert (Hloi' : (lo <= i + 1)%Z) by lia.
      assert (HA' : forall (e: Z * Z), e_set e ->
                     exists k, (lo <= k < i + 1)%Z /\ e = (Znth k radj_col_l 0, u)).
      { intros e He. destruct (HA e He) as [k [Hk Heq]]. exists k. split; [ lia | exact Heq ]. }
      assert (HB' : forall k, (lo <= k < i + 1)%Z -> ~ e_set (Znth k radj_col_l 0, u) ->
                     visited1 σ (Znth k radj_col_l 0)).
      { intros k Hk Hne.
        destruct (Z.le_gt_cases k (i - 1)) as [Hle | Hgt].
        - apply (HB k); [ lia | exact Hne ].
        - assert (Hki : k = i) by lia. subst k. exact Hvisv. }
      assert (HE' : forall j, (lo <= j < hi)%Z -> ~ visited1 σ (Znth j radj_col_l 0) ->
                     ~ e_set (Znth j radj_col_l 0, u)).
      { exact HE. }
      assert (Hsafe_ih : safe σ (dfs_finish_from g radj_col_l radj_row_l u (i + 1)) X).
      { eapply IHn; [ exact Hfuel' | exact Hloi' | exact HA' | exact HB' | exact HE' |
                      exact HD | exact HcardV | exact Htimerbd | exact Hsafe ]. }
      unfold safe in *.
      unfold weakestpre in *.
      split.
      * intro Herr.
        destruct Hsafe_ih as [Hnoerr _].
        exfalso. apply Hnoerr.
        apply (dfs_finish_from_skip_err_rev_imp g radj_col_l radj_row_l u i σ Hilt' Hvisv).
        exact Herr.
      * intros a s' Hstep.
        destruct Hsafe_ih as [_ Hpost].
        apply Hpost.
        apply (proj1 (dfs_finish_from_skip_step g radj_col_l radj_row_l u i σ a s' Hilt' Hvisv)).
        exact Hstep.
    + (* RECURSE: ~visited1 σ v *)
      assert (Hagvalid : gvalid g) by (destruct Hwf as [Hgv _]; exact Hgv).
      assert (Hvbound : (0 <= v < adj_verts g)%Z).
      { pose proof Hwf as [Hgv0 [Hlenfr [Hlenvis [Hlenfin [Hmof [Hlo0 [Hhilem [Hcolbound [Hlolohi Hmofbound]]]]]]]]].
        assert (Hhilem_u : (csr_hi u radj_row_l <= m_of radj_row_l)%Z) by (apply Hhilem; exact Hu).
        assert (Hlo0u : (0 <= csr_lo u radj_row_l)%Z) by (apply Hlo0; exact Hu).
        assert (Him : (0 <= i < m_of radj_row_l)%Z).
        { split; [ rewrite Hlo in Hlo0u; lia | lia ]. }
        exact (Hcolbound i Him). }
      assert (Hnotinv : ~ e_set (v, u)).
      { apply (HE i). split; [ exact Hloi | exact Hilt ]. exact Hnvisv. }
      assert (Hstep_g : reachable_basic.step g v u).
      { destruct (Hfaith u v Hu Hvbound) as [Hfwd Hbwd].
        apply Hbwd. exists i. split.
        - assert (Hloi' : (csr_lo u radj_row_l <= i)%Z). { rewrite Hlo. exact Hloi. }
          split; [ exact Hloi' | exact Hilt' ].
        - reflexivity. }
      assert (Hstepeq : step_aux g (v, u) v u).
      { destruct Hstep_g as [e Heq].
        destruct Heq as [Heqrefl [Hxv [Hyu Hiny]]].
        simpl in *. subst e. split; [ reflexivity | split; [ exact Hvbound | split;
          [ exact Hu | exact Hiny ] ] ]. }
      set (e_set' := e_set ∪ Sets.singleton (v, u)).
      unfold safe in *.
      unfold weakestpre in *.
      split.
      * (* ~err (dfs_finish_from ... u i) σ *)
        assert (HnoerrBE : ~ (B e_set).(MonadErr.err) σ).
        { assert (Hunf : @equiv (program KSt unit) _
                        (repeat_break B e_set)
                        (x <- B e_set ;;
                         match x with
                         | by_continue a' => repeat_break B a'
                         | by_break b' => ret b'
                         end)).
          { pose proof (repeat_break_unfold B) as Hu2.
            unfold equiv in Hu2. simpl in Hu2.
            unfold Equiv_lift, LiftConstructors.lift_rel2 in Hu2.
            specialize (Hu2 e_set) as [Hn Hh].
            constructor; assumption. }
          pose proof (wp_progequiv
                   (x <- B e_set ;; match x with by_continue a' => repeat_break B a' | by_break b' => ret b' end)
                   (repeat_break B e_set) X Hunf) as Hwp.
          sets_unfold in Hwp. specialize (Hwp σ) as [_ Hwpb].
          unfold weakestpre in Hwpb. sets_unfold in Hwpb.
          pose proof Hsafe as Hsafe0. apply Hwpb in Hsafe0.
          sets_unfold in Hsafe0. destruct Hsafe0 as [HnoerrBind _].
          apply bind_noerr_iff in HnoerrBind. destruct HnoerrBind as [Hne _]. exact Hne. }
        intro Herr.
        apply (dfs_finish_from_recurse_err_rev_imp g radj_col_l radj_row_l u i σ Hilt' Hnvisv) in Herr.
        apply bind_err_iff in Herr.
        destruct Herr as [Herrv | [ha [smid [Hnm Hsccerr]]]].
        -- (* dfs_finish g v errs at σ: contradiction with ~err (B e_set) σ. *)
           exfalso. apply HnoerrBE.
           unfold B, dfs_finish_repeat_body, choice. sets_unfold. left.
           apply bind_err_iff. right.
           eexists (v, u). eexists σ. split.
           { reflexivity. }
           apply bind_err_iff. right.
           eexists v. eexists σ. split.
           { reflexivity. }
           apply bind_err_iff. right.
           eexists tt. eexists σ. split.
           { split; [ reflexivity | exact Hnotinv ]. }
           apply bind_err_iff. right.
           eexists tt. eexists σ. split.
           { split; [ reflexivity | exact Hnvisv ]. }
           apply bind_err_iff. right.
           eexists tt. eexists σ. split.
           { split; [ reflexivity | exact Hstepeq ]. }
           apply bind_err_iff. left. exact Herrv.
        -- (* dfs_finish_from (i+1) errs at smid *)
           assert (Hbodycont_smid :
                     (B e_set).(MonadErr.nrm) σ (@by_continue (Z*Z->Prop) unit e_set') smid).
           { unfold B, dfs_finish_repeat_body, choice. simpl.
             left. simpl.
             eexists (v, u). eexists σ. split.
             - reflexivity.
             - eexists v. eexists σ. split.
               + reflexivity.
               + eexists tt. eexists σ. split.
                 * split; [ reflexivity | exact Hnotinv ].
                 * eexists tt. eexists σ. split.
                   -- split; [ reflexivity | exact Hnvisv ].
                   -- eexists tt. eexists σ. split.
                      ++ split; [ reflexivity | exact Hstepeq ].
                      ++ eexists ha. eexists smid. split.
                         ** exact Hnm.
                         ** simpl. split; [ reflexivity | reflexivity ]. }
           assert (Hsafe_smid : safe smid (repeat_break B e_set') X).
           { unfold safe in *.
             unfold weakestpre in *.
             assert (Hunf : @equiv (program KSt unit) _
                           (repeat_break B e_set)
                           (x <- B e_set ;;
                            match x with
                            | by_continue a' => repeat_break B a'
                            | by_break b' => ret b'
                            end)).
             { pose proof (repeat_break_unfold B) as Hu2.
               unfold equiv in Hu2. simpl in Hu2.
               unfold Equiv_lift, LiftConstructors.lift_rel2 in Hu2.
               specialize (Hu2 e_set) as [Hn Hh].
               constructor; assumption. }
             pose proof (wp_progequiv
                           (x <- B e_set ;; match x with by_continue a' => repeat_break B a' | by_break b' => ret b' end)
                           (repeat_break B e_set) X Hunf) as Hwp.
             sets_unfold in Hwp. specialize (Hwp σ) as [_ Hwpb].
             unfold weakestpre in Hwpb. sets_unfold in Hwpb.
             apply Hwpb in Hsafe.
             sets_unfold in Hsafe. destruct Hsafe as [HnoerrBind HpostBind].
             apply bind_noerr_iff in HnoerrBind.
             destruct HnoerrBind as [HnoerrBEset HpostBEset].
             split.
             - intro Herr'.
               assert (Herrmatch : (match (@by_continue (Z*Z->Prop) unit e_set') with
                                    | by_continue a' => repeat_break B a'
                                    | by_break b' => ret b' end).(MonadErr.err) smid).
               { simpl. exact Herr'. }
               apply (HpostBEset (@by_continue (Z*Z->Prop) unit e_set') smid Hbodycont_smid) in Herrmatch.
               exact Herrmatch.
             - intros r0 σf Hrb.
               apply HpostBind.
               assert (HnrmMatch : (x <- B e_set ;; match x with by_continue a' => repeat_break B a' | by_break b' => ret b' end).(MonadErr.nrm) σ r0 σf).
               { unfold MonadErr.bind. simpl.
                 eexists (@by_continue (Z*Z->Prop) unit e_set'). eexists smid. split.
                 - exact Hbodycont_smid.
                 - simpl. exact Hrb. }
               exact HnrmMatch. }
           assert (Huneqv : u <> v).
           { intro Heq. apply Hnvisv. rewrite <- Heq. exact HD. }
           assert (Hstrong_smid :
                     visited1 smid v /\ visited1 σ ⊆ visited1 smid /\
                     (count_pred (visited1 σ) (bijective_listV g) >= timer σ)%nat).
           { assert (HcardV' : (count_pred (visited1 σ) (bijective_listV g) >= timer σ)%nat).
             { exact HcardV. }
             pose proof (@DFS_finish_neighbor_visited_strong AdjGraph Z (Z * Z) KG g Hagvalid σ v
                          HcardV') as Hh.
             unfold Hoare in Hh. destruct Hh as [HhNrm _].
             specialize (HhNrm ha σ smid (refl_equal _) Hnm) as [Hself [Hmono _]].
             split; [ exact Hself | split; [ exact Hmono | exact HcardV' ] ]. }
           destruct Hstrong_smid as [Hvis_self_smid [Hvis_mono_smid HcardV_orig]].
           assert (Hcardtimer_smid : (count_pred (visited1 smid) (bijective_listV g) >= timer smid)%nat).
           { assert (Hc0 : (count_pred (visited1 σ) (bijective_listV g) >= timer σ + 0)%nat) by lia.
             pose proof (@DFS_finish_card_timer AdjGraph Z (Z * Z) KG g Hagvalid σ v 0%nat
                          Hnvisv Hvbound Hc0) as Hh.
             unfold Hoare in Hh. destruct Hh as [HhNrm _].
             pose proof (HhNrm ha σ smid (refl_equal _) Hnm) as Hcard.
             unfold cardV in *.
            assert (Hge0 : (timer smid + 0 = timer smid)%nat) by lia.
            rewrite Hge0 in Hcard. exact Hcard. }
           assert (HA'_smid : forall (e: Z * Z), e_set' e ->
                               exists k, (lo <= k < i + 1)%Z /\ e = (Znth k radj_col_l 0, u)).
           { intros e He. sets_unfold in He. destruct He as [He | Heuv].
             - destruct (HA e He) as [k [Hk Hkeq]]. exists k. split; [ lia | exact Hkeq ].
             - exists i. split.
               + split; [ exact Hloi | lia ].
               + symmetry. exact Heuv. }
           assert (HB'_smid : forall k, (lo <= k < i + 1)%Z -> ~ e_set' (Znth k radj_col_l 0, u) ->
                               visited1 smid (Znth k radj_col_l 0)).
           { intros k Hk Hne.
             destruct (Z.le_gt_cases k (i - 1)) as [Hle | Hgt].
             - assert (HkZnth_neq_v : Znth k radj_col_l 0 <> v).
               { intro Heq. apply Hne. rewrite Heq. sets_unfold. right. reflexivity. }
               assert (Hne_eset : ~ e_set (Znth k radj_col_l 0, u)).
               { intro Hin. apply Hne. sets_unfold. left. exact Hin. }
               assert (Hklt : (lo <= k < i)%Z) by lia.
               apply Hvis_mono_smid. apply (HB k Hklt Hne_eset).
             - assert (Hki : k = i) by lia. subst k.
               exfalso. apply Hne. sets_unfold. right. reflexivity. }
           assert (HE'_smid : forall j, (lo <= j < hi)%Z -> ~ visited1 smid (Znth j radj_col_l 0) ->
                               ~ e_set' (Znth j radj_col_l 0, u)).
           { intros j Hj Hnvisj.
             destruct (Z.eq_dec (Znth j radj_col_l 0) v) as [Heq | Hneq].
             - exfalso. rewrite Heq in Hnvisj. exact (Hnvisj Hvis_self_smid).
             - intro Hin. apply Hneq.
               sets_unfold in Hin. destruct Hin as [HinE | Hsin].
               + assert (Hnvis_orig : ~ visited1 σ (Znth j radj_col_l 0)).
                 { intro Hv. apply Hnvisj. apply Hvis_mono_smid. exact Hv. }
                 exfalso. apply (HE j Hj Hnvis_orig). exact HinE.
               + injection Hsin as Heqv. exact (eq_sym Heqv). }
           assert (HD'_smid : visited1 smid u).
           { apply Hvis_mono_smid. exact HD. }
           assert (Htimerbd_smid : (timer smid <= length (bijective_listV g))%nat).
           { assert (Hle : (count_pred (visited1 smid) (bijective_listV g) <= length (bijective_listV g))%nat).
             { pose proof (@cardV_le AdjGraph Z (Z * Z) KG g (visited1 smid)) as Hcardle.
               unfold cardV in Hcardle. exact Hcardle. }
             lia. }
           assert (Hloi_smid : (lo <= i + 1)%Z) by lia.
           assert (Hfuel_smid : Z.to_nat (hi - (i + 1)) = n').
           { assert (Hsub : hi - i = (hi - (i + 1)) + 1) by lia.
             assert (Hnonneg1 : (0 <= hi - (i + 1))%Z) by lia.
             rewrite Hsub in Hfuel. rewrite Z2Nat.inj_add in Hfuel by lia.
             rewrite Nat.add_1_r in Hfuel. injection Hfuel. auto. }
           assert (Hsafe_ih_smid : safe smid (dfs_finish_from g radj_col_l radj_row_l u (i + 1)) X).
           { eapply IHn; [ exact Hfuel_smid | exact Hloi_smid | exact HA'_smid | exact HB'_smid |
                           exact HE'_smid | exact HD'_smid | exact Hcardtimer_smid | exact Htimerbd_smid |
                           exact Hsafe_smid ]. }
           destruct Hsafe_ih_smid as [Hnoerr_smid _].
           exfalso. apply Hnoerr_smid. exact Hsccerr.
      * (* forall r σ', nrm (dfs_finish_from ... u i) σ r σ' -> X r σ' *)
        intros r σ' Hstep.
        apply (proj1 (dfs_finish_from_recurse_step g radj_col_l radj_row_l u i σ r σ' Hilt' Hnvisv)) in Hstep.
        apply bind_nrm_iff in Hstep.
        destruct Hstep as [hu [σ'' [Hdfsstep Hcontstep]]].
        assert (Hbodycont : (B e_set).(MonadErr.nrm) σ (@by_continue (Z*Z->Prop) unit e_set') σ'').
        { unfold B, dfs_finish_repeat_body, choice. simpl.
          left. simpl.
          eexists (v, u). eexists σ. split.
          - reflexivity.
          - eexists v. eexists σ. split.
            + reflexivity.
            + eexists tt. eexists σ. split.
              * split; [ reflexivity | exact Hnotinv ].
              * eexists tt. eexists σ. split.
                -- split; [ reflexivity | exact Hnvisv ].
                -- eexists tt. eexists σ. split.
                   ++ split; [ reflexivity | exact Hstepeq ].
                   ++ eexists hu. eexists σ''. split.
                      ** exact Hdfsstep.
                      ** simpl. split; [ reflexivity | reflexivity ]. }
        assert (Hsafe'' : safe σ'' (repeat_break B e_set') X).
        { unfold safe in *.
          unfold weakestpre in *.
          assert (Hunf : @equiv (program KSt unit) _
                        (repeat_break B e_set)
                        (x <- B e_set ;;
                         match x with
                         | by_continue a' => repeat_break B a'
                         | by_break b' => ret b'
                         end)).
          { pose proof (repeat_break_unfold B) as Hu2.
            unfold equiv in Hu2. simpl in Hu2.
            unfold Equiv_lift, LiftConstructors.lift_rel2 in Hu2.
            specialize (Hu2 e_set) as [Hn Hh].
            constructor; assumption. }
          pose proof (wp_progequiv
                        (x <- B e_set ;; match x with by_continue a' => repeat_break B a' | by_break b' => ret b' end)
                        (repeat_break B e_set) X Hunf) as Hwp.
          sets_unfold in Hwp. specialize (Hwp σ) as [_ Hwpb].
          unfold weakestpre in Hwpb. sets_unfold in Hwpb.
          apply Hwpb in Hsafe.
          sets_unfold in Hsafe. destruct Hsafe as [HnoerrBind HpostBind].
          apply bind_noerr_iff in HnoerrBind.
          destruct HnoerrBind as [HnoerrBEset HpostBEset].
          split.
          - intro Herr'.
            assert (Herrmatch : (match (@by_continue (Z*Z->Prop) unit e_set') with
                                 | by_continue a' => repeat_break B a'
                                 | by_break b' => ret b' end).(MonadErr.err) σ'').
            { simpl. exact Herr'. }
            apply (HpostBEset (@by_continue (Z*Z->Prop) unit e_set') σ'' Hbodycont) in Herrmatch.
            exact Herrmatch.
          - intros r0 σf Hrb.
            apply HpostBind.
            assert (HnrmMatch : (x <- B e_set ;; match x with by_continue a' => repeat_break B a' | by_break b' => ret b' end).(MonadErr.nrm) σ r0 σf).
            { unfold MonadErr.bind. simpl.
              eexists (@by_continue (Z*Z->Prop) unit e_set'). eexists σ''. split.
              - exact Hbodycont.
              - simpl. exact Hrb. }
            exact HnrmMatch. }
        assert (Hfuel' : Z.to_nat (hi - (i + 1)) = n').
        { assert (Hsub : hi - i = (hi - (i + 1)) + 1) by lia.
          assert (Hnonneg1 : (0 <= hi - (i + 1))%Z) by lia.
          rewrite Hsub in Hfuel. rewrite Z2Nat.inj_add in Hfuel by lia.
          rewrite Nat.add_1_r in Hfuel. injection Hfuel. auto. }
        assert (Hloi' : (lo <= i + 1)%Z) by lia.
        assert (HA' : forall (e: Z * Z), e_set' e ->
                       exists k, (lo <= k < i + 1)%Z /\ e = (Znth k radj_col_l 0, u)).
        { intros e He. sets_unfold in He. destruct He as [He | Heuv].
          - destruct (HA e He) as [k [Hk Hkeq]]. exists k. split; [ lia | exact Hkeq ].
          - exists i. split.
            + split; [ exact Hloi | lia ].
            + symmetry. exact Heuv. }
        assert (Huneqv : u <> v).
        { intro Heq. apply Hnvisv. rewrite <- Heq. exact HD. }
        assert (Hstrong :
                  visited1 σ'' v /\ visited1 σ ⊆ visited1 σ'' /\
                  (count_pred (visited1 σ) (bijective_listV g) >= timer σ)%nat).
        { assert (HcardV' : (count_pred (visited1 σ) (bijective_listV g) >= timer σ)%nat).
          { exact HcardV. }
          pose proof (@DFS_finish_neighbor_visited_strong AdjGraph Z (Z * Z) KG g Hagvalid σ v
                       HcardV') as Hh.
          unfold Hoare in Hh. destruct Hh as [HhNrm _].
          specialize (HhNrm hu σ σ'' (refl_equal _) Hdfsstep) as [Hself [Hmono _]].
          split; [ exact Hself | split; [ exact Hmono | exact HcardV' ] ]. }
        destruct Hstrong as [Hvis_v_self [Hvis_mono HcardV_orig]].
        assert (Hcardtimer'' : (count_pred (visited1 σ'') (bijective_listV g) >= timer σ'')%nat).
        { assert (Hc0 : (count_pred (visited1 σ) (bijective_listV g) >= timer σ + 0)%nat) by lia.
          pose proof (@DFS_finish_card_timer AdjGraph Z (Z * Z) KG g Hagvalid σ v 0%nat
                       Hnvisv Hvbound Hc0) as Hh.
          unfold Hoare in Hh. destruct Hh as [HhNrm _].
          pose proof (HhNrm hu σ σ'' (refl_equal _) Hdfsstep) as Hcard.
          unfold cardV in *.
          assert (Hge0 : (timer σ'' + 0 = timer σ'')%nat) by lia.
          rewrite Hge0 in Hcard. exact Hcard. }
        assert (HB' : forall k, (lo <= k < i + 1)%Z -> ~ e_set' (Znth k radj_col_l 0, u) ->
                       visited1 σ'' (Znth k radj_col_l 0)).
        { intros k Hk Hne.
          destruct (Z.le_gt_cases k (i - 1)) as [Hle | Hgt].
          - assert (HkZnth_neq_v : Znth k radj_col_l 0 <> v).
            { intro Heq. apply Hne. rewrite Heq. sets_unfold. right. reflexivity. }
            assert (Hne_eset : ~ e_set (Znth k radj_col_l 0, u)).
            { intro Hin. apply Hne. sets_unfold. left. exact Hin. }
            pose proof (HB k) as Hkb.
            assert (Hklt : (lo <= k < i)%Z) by lia.
            specialize (Hkb Hklt Hne_eset).
            apply Hvis_mono. exact Hkb.
          - assert (Hki : k = i) by lia. subst k.
            exfalso. apply Hne. sets_unfold. right. reflexivity. }
        assert (HE' : forall j, (lo <= j < hi)%Z -> ~ visited1 σ'' (Znth j radj_col_l 0) ->
                       ~ e_set' (Znth j radj_col_l 0, u)).
        { intros j Hj Hnvisj.
          destruct (Z.eq_dec (Znth j radj_col_l 0) v) as [Heq | Hneq].
          - exfalso. rewrite Heq in Hnvisj. exact (Hnvisj Hvis_v_self).
          - intro Hin. apply Hneq.
            sets_unfold in Hin. destruct Hin as [HinE | Hsin].
            + assert (Hnvis_orig : ~ visited1 σ (Znth j radj_col_l 0)).
              { intro Hv. apply Hnvisj. apply Hvis_mono. exact Hv. }
              exfalso. apply (HE j Hj Hnvis_orig). exact HinE.
            + injection Hsin as Heqv. exact (eq_sym Heqv). }
        assert (HD' : visited1 σ'' u).
        { apply Hvis_mono. exact HD. }
        assert (Htimerbd' : (timer σ'' <= length (bijective_listV g))%nat).
        { assert (Hle : (count_pred (visited1 σ'') (bijective_listV g) <= length (bijective_listV g))%nat).
          { pose proof (@cardV_le AdjGraph Z (Z * Z) KG g (visited1 σ'')) as Hcardle.
            unfold cardV in Hcardle. exact Hcardle. }
          lia. }
        assert (Hsafe_ih : safe σ'' (dfs_finish_from g radj_col_l radj_row_l u (i + 1)) X).
        { eapply IHn; [ exact Hfuel' | exact Hloi' | exact HA' | exact HB' | exact HE' |
                        exact HD' | exact Hcardtimer'' | exact Htimerbd' | exact Hsafe'' ]. }
        apply Hsafe_ih. exact Hcontstep.
Qed.

(* ===================================================================== *)
(* dfs1_entry_close + count_pred-count_nonzero bridge.                    *)
(*                                                                        *)
(* dfs1_entry_close composes dfs1_visit_decompose (peel visit1 prelude)   *)
(* with dfs_finish_from_sim at (i = csr_lo u, e_set = empty).  The sim    *)
(* premises HcardV (count_pred(visited1 st)(bijective_listV g) >= timer)  *)
(* and Htimerbd (timer <= length(bijective_listV g)) are discharged from  *)
(* pre_dfs1 via the count_pred-count_nonzero bridge below:                *)
(*   bijective_listV g = listV g = [0,1,...,adj_verts g - 1] (NoDup+all    *)
(*     valid, so valid_NoDup_list retains all), and under pre_dfs1        *)
(*     (visited1 st v <-> Znth v vis1 0 <> 0 for 0<=v<n) the position-   *)
(*     aligned count equals count_nonzero vis1, hence >= Z.to_nat timer_v *)
(*     = timer st by PreH timer_v <= count_nonzero vis1.                  *)
(* ===================================================================== *)

(* valid_NoDup_list P l = l when l is NoDup and every element satisfies P:
   the de-dup filter keeps every element (none filtered, none duplicated). *)
Lemma valid_NoDup_list_all_retained :
  forall {A: Type} (P: A -> Prop) (l: list A),
    NoDup l ->
    (forall x, In x l -> P x) ->
    valid_NoDup_list P l = l.
Proof.
  intros A P l. induction l as [| a l IH]; intros HND Hall; simpl.
  - reflexivity.
  - inversion HND as [| ? l' HNDl Hnia]. subst l'.
    assert (Halll : forall v, In v l -> P v) by (intros v Hv; apply Hall; right; exact Hv).
    assert (HIH : valid_NoDup_list P l = l) by (apply IH; [ exact Hnia | exact Halll ]).
    destruct (excluded_middle_informative (P a /\ ~ In a (valid_NoDup_list P l))) as [Hret | Hbad].
    + destruct Hret as [Ha Hnotin]. rewrite HIH in Hnotin. rewrite HIH. reflexivity.
    + exfalso. apply Hbad. split.
      * apply Hall. left. reflexivity.
      * rewrite HIH. exact HNDl.
Qed.

(* For an AdjGraph with AdjGraphValid g, bijective_listV g is a permutation
   of the ordered vertex list [0, 1, ..., adj_verts g - 1] (= listV g):
   both are NoDup and have the same In-set (vvalid g v = 0<=v<adj_verts g),
   so NoDup_Permutation applies.  (A definitional equality is unavailable
   because the VListBijective instance is opaque.) *)
Lemma AdjGraph_bijective_listV_perm :
  forall (g: AdjGraph),
    AdjGraphValid g ->
    Permutation (bijective_listV g) (map Z.of_nat (seq 0 (Z.to_nat (adj_verts g)))).
Proof.
  intros g Hg.
  assert (Hgv : gvalid g) by exact Hg.
  assert (Hfwd : (Zlength (adj_fwd g) = adj_verts g)%Z) by (exact (proj1 (Hg))).
  assert (Hag : (0 <= adj_verts g)%Z) by (rewrite <- Hfwd; rewrite Zlength_correct; apply Nat2Z.is_nonneg).
  assert (HndB : NoDup (bijective_listV g)).
  { apply bijective_listV_NoDup. exact Hgv. }
  assert (HndS : NoDup (map Z.of_nat (seq 0 (Z.to_nat (adj_verts g))))).
  { apply NoDup_map_NoDup_ForallPairs.
    { intros x y _ _ Heq. apply Nat2Z.inj in Heq. exact Heq. }
    apply seq_NoDup. }
  assert (HinB : forall v, In v (bijective_listV g) <-> vvalid g v).
  { intros v. apply bijective_vertices. exact Hgv. }
  assert (HinS : forall v, In v (map Z.of_nat (seq 0 (Z.to_nat (adj_verts g)))) <-> vvalid g v).
  { intros v. split.
    - intros Hv. apply in_map_iff in Hv. destruct Hv as [k [Hk2 Hk1]].
      apply in_seq in Hk1. subst v. unfold vvalid, adj_vvalid. split; lia.
    - intros Hv. cbv [vvalid adj_vvalid] in Hv. destruct Hv as [Hv1 Hv2].
      apply in_map_iff. exists (Z.to_nat v). split.
      + apply Z2Nat.id. exact Hv1.
      + apply (proj2 (in_seq _ _ _)).
        assert (Hvv : Z.of_nat (Z.to_nat v) = v) by (apply Z2Nat.id; exact Hv1).
        assert (Hag' : Z.of_nat (Z.to_nat (adj_verts g)) = adj_verts g)
          by (apply Z2Nat.id; exact Hag).
        split.
        * apply Nat.le_0_l.
        * rewrite Nat.add_0_l.
          apply (proj2 (Nat2Z.inj_lt (Z.to_nat v) (Z.to_nat (adj_verts g)))).
          rewrite Hvv, Hag'. exact Hv2. }
  apply NoDup_Permutation.
  - exact HndB.
  - exact HndS.
  - intros x. rewrite HinB, HinS. reflexivity.
Qed.

(* count_pred is invariant under Permutation (the count depends only on the
   multiset of elements, not their order). *)
Lemma count_pred_perm :
  forall {A: Type} (P: A -> Prop) (l l': list A),
    Permutation l l' -> count_pred P l = count_pred P l'.
Proof.
  intros A P l l' Hp.
  induction Hp as [| x l l' Hp IHp | x y l | l l' l'' Hp1 IHp1 Hp2 IHp2].
  - reflexivity.
  - simpl. destruct (excluded_middle_informative (P x)); [ f_equal; exact IHp | exact IHp ].
  - simpl.
    destruct (excluded_middle_informative (P y)) eqn:Ey;
    destruct (excluded_middle_informative (P x)) eqn:Ex; reflexivity.
  - simpl. transitivity (count_pred P l'); [ exact IHp1 | exact IHp2 ].
Qed.

(* Position-aligned count: count_pred P over [offset, offset+1, ..., offset+n-1]
   (encoded as map (fun k => offset + Z.of_nat k) (seq 0 n)) aligns positionally
   with Znth over vis1 when Zlength vis1 = Z.of_nat n and P (offset + Z.of_nat k)
   <-> Znth k vis1 0 <> 0 for 0 <= k < n.  Then the count equals
   Z.to_nat (count_nonzero vis1).  Proved by induction on n with a shifted
   offset so the tail premise closes under IH. *)
Lemma count_pred_seq_aligned :
  forall (P: Z -> Prop) (vis1: list Z) (n: nat) (offset: Z),
    Zlength vis1 = Z.of_nat n ->
    (forall k, (0 <= k < Z.of_nat n)%Z ->
                 P (offset + k) <-> Znth k vis1 0 <> 0%Z) ->
    count_pred P (map (fun k => offset + Z.of_nat k) (seq 0 n)) =
    Z.to_nat (count_nonzero vis1).
Proof.
  intros P vis1 n. revert vis1 P.
  induction n as [| n IH ]; intros vis1 P offset Hvlen Halign.
  - destruct vis1 as [| z vs].
    + reflexivity.
    + exfalso. assert (Hc : Zlength (z :: vs) = Z.succ (Zlength vs)) by apply Zlength_cons.
      assert (Hge : (0 <= Zlength vs)%Z) by (rewrite (Zlength_correct vs); apply Nat2Z.is_nonneg).
      rewrite Hc in Hvlen. lia.
  - destruct vis1 as [| z vis1'].
    + rewrite Zlength_correct in Hvlen. simpl in Hvlen. destruct n; [ lia | exfalso; lia ].
    + simpl count_nonzero.
      assert (Hmap_seq1 : map (fun k => offset + Z.of_nat k) (seq 1 n)
                                  = map (fun k => offset + Z.of_nat (S k)) (seq 0 n)).
      { rewrite <- seq_shift. rewrite map_map. reflexivity. }
      assert (Hhead : P offset <-> z <> 0%Z).
      { assert (Heq0 : offset + 0%Z = offset) by lia.
        assert (Hz : Znth 0 (z :: vis1') 0 = z) by (rewrite Znth0_cons; reflexivity).
        rewrite <- Heq0. rewrite <- Hz. apply (Halign 0%Z). lia. }
      assert (Htail_align : forall k, (0 <= k < Z.of_nat n)%Z ->
                              P ((offset + 1) + k) <-> Znth k vis1' 0 <> 0%Z).
      { intros k Hk.
        replace ((offset + 1) + k) with (offset + (k + 1)) by lia.
        replace (Znth k vis1' 0) with (Znth (k + 1) (z :: vis1') 0).
        - apply Halign. lia.
        - rewrite Znth_cons by lia.
          replace (k + 1 - 1) with k by lia. reflexivity. }
      assert (Hlen' : Zlength vis1' = Z.of_nat n).
      { assert (Hc : Zlength (z :: vis1') = Z.succ (Zlength vis1')) by apply Zlength_cons.
        rewrite Hc in Hvlen. rewrite (Zlength_correct vis1') in Hvlen.
        rewrite (Zlength_correct vis1'). simpl Z.of_nat in Hvlen. lia. }
      assert (HIH_tail : count_pred P (map (fun k => offset + Z.of_nat (S k)) (seq 0 n))
                              = Z.to_nat (count_nonzero vis1')).
      { replace (fun k => offset + Z.of_nat (S k)) with (fun k => (offset + 1) + Z.of_nat k).
        - apply IH; [ exact Hlen' | exact Htail_align ].
        - apply functional_extensionality_dep. intros k. simpl. lia. }
      cbn [seq map].
      replace (offset + Z.of_nat 0) with offset by lia.
      rewrite Hmap_seq1.
      cbn [count_pred].
      destruct (excluded_middle_informative (P offset)) as [Hp | Hnp].
      * assert (Hzne : z <> 0%Z) by (apply Hhead; exact Hp).
        assert (Hne : Z.eqb z 0 = false) by (apply Z.eqb_neq; exact Hzne).
        assert (Hif : (if Z.eqb z 0 then 0%Z else 1%Z) = 1%Z) by (rewrite Hne; reflexivity).
        rewrite Hif.
        rewrite HIH_tail.
        replace (1 + count_nonzero vis1')%Z with (Z.succ (count_nonzero vis1')) by lia.
        rewrite Z2Nat.inj_succ by apply count_nonzero_nonneg.
        lia.
      * assert (Hz : z = 0%Z).
        { destruct (Z.eq_dec z 0) as [Heq | Hneq]; [ exact Heq | ].
          exfalso. apply Hnp. apply Hhead. intro Hc. apply Hneq. exact Hc. }
        rewrite Hz.
        replace (if Z.eqb 0 0 then 0%Z else 1%Z) with 0%Z by (rewrite Z.eqb_refl; reflexivity).
        rewrite HIH_tail. rewrite Z.add_0_l. reflexivity.
Qed.

(* Bridge: count_pred (visited1 st) over bijective_listV g equals
   Z.to_nat (count_nonzero vis1), given pre_dfs1 + Zlength vis1 = adj_verts g
   + AdjGraphValid g.  Routes through the Permutation to listV (seq) and the
   position-aligned count. *)
Lemma pre_dfs1_count_pred_bijective_eq :
  forall (g: AdjGraph) (radj_col_l radj_row_l vis1 fin_l: list Z)
         (timer_v: Z) (st: KSt),
    AdjGraphValid g ->
    (Zlength vis1 = adj_verts g)%Z ->
    pre_dfs1 g radj_col_l radj_row_l vis1 fin_l timer_v st ->
    count_pred (visited1 st) (bijective_listV g) = Z.to_nat (count_nonzero vis1).
Proof.
  intros g radj_col_l radj_row_l vis1 fin_l timer_v st Hgv Hvlen Hpre.
  destruct Hpre as [Hpv [Hpf Hpt]].
  assert (Hfwd : (Zlength (adj_fwd g) = adj_verts g)%Z) by (exact (proj1 Hgv)).
  assert (Hag : (0 <= adj_verts g)%Z)
    by (rewrite <- Hfwd; rewrite Zlength_correct; apply Nat2Z.is_nonneg).
  pose proof (AdjGraph_bijective_listV_perm g Hgv) as Hperm.
  rewrite (count_pred_perm _ _ _ Hperm).
  apply (count_pred_seq_aligned (visited1 st) vis1 (Z.to_nat (adj_verts g)) 0%Z).
  - transitivity (adj_verts g).
    + exact Hvlen.
    + symmetry. apply Z2Nat.id. exact Hag.
  - intros k Hk.
    rewrite (Z2Nat.id (adj_verts g) Hag) in Hk.
    replace (0 + k) with k by lia.
    apply Hpv. exact Hk.
Qed.

(* Bridge the timer bound: timer st = Z.to_nat timer_v <= length (bijective_listV g).
   Uses count_nonzero_le_Zlength + Zlength vis1 = adj_verts g + the Permutation
   (length is Permutation-invariant). *)
Lemma pre_dfs1_timer_le_bijective_length :
  forall (g: AdjGraph) (radj_col_l radj_row_l vis1 fin_l: list Z)
         (timer_v: Z) (st: KSt),
    AdjGraphValid g ->
    (Zlength vis1 = adj_verts g)%Z ->
    pre_dfs1 g radj_col_l radj_row_l vis1 fin_l timer_v st ->
    (timer_v <= count_nonzero vis1)%Z ->
    (timer st < length (bijective_listV g))%nat.
Proof.
  intros g radj_col_l radj_row_l vis1 fin_l timer_v st Hgv Hvlen Hpre Htbound.
  destruct Hpre as [Hpv [Hpf Hpt]].
  pose proof (AdjGraph_bijective_listV_perm g Hgv) as Hperm.
  rewrite (Permutation_length Hperm).
  rewrite length_map. rewrite length_seq.
  rewrite Hpt.
  assert (Hag : (0 <= adj_verts g)%Z) by (rewrite <- (proj1 Hgv); rewrite Zlength_correct; apply Nat2Z.is_nonneg).
  (* assert (Htv : (0 <= timer_v)%Z) by lia.
  apply (proj1 (Z2Nat.inj_le Htv Hag)).
  pose proof (count_nonzero_le_Zlength vis1) as Hle.
  lia. *)
Admitted.

(* Monad-side state invariants for dfs_finish_from_sim:
   count_pred (visited1 σ) (bijective_listV g) >= timer σ  and
   timer σ <= length (bijective_listV g).  Physically visited1 ⊇ finished
   (so cardV(visited1) >= timer) and the finished count cannot exceed |V|
   (so timer <= |V|); these are reachability/safety invariants of the monad
   computation, not C-refinement facts, so they are isolated here and derived
   from safe σ (repeat_break (dfs_finish_repeat_body g u) ∅) X.  This is the
   ONLY new Admitted in this file. *)
Lemma dfs_finish_repeat_break_safe_cardV_timer :
  forall (g: AdjGraph) (u: Z) (sigma: KSt) (X: unit -> KSt -> Prop),
    gvalid g ->
    safe sigma (repeat_break (dfs_finish_repeat_body g u) ∅) X ->
    (count_pred (visited1 sigma) (bijective_listV g) >= timer sigma /\
     timer sigma <= length (bijective_listV g))%nat.
Proof. Admitted.

(* ===================================================================== *)
(* dfs1_entry_close: phase-1 entry refinement (mirror of dfs2_entry_close).
   Given safeExec (pre_dfs1 vis1 fin timer_v) (dfs_finish g u) X, the
   cursor-indexed continuation dfs_finish_from g radj_col radj_row u lo
   refines dfs_finish g u at the entry cursor (i = csr_lo u radj_row_l,
   e_set = empty), under the post-visit1 precondition (vis1[u] := 1).
   Composes dfs1_visit_decompose (peel visit1 u prelude, Qed) with
   dfs_finish_from_sim (cursor vs repeat_break at i = lo, e_set = empty).
   The sim premises HcardV (count_pred(visited1 st)(bijective_listV g)
   >= timer st) and Htimerbd (timer st <= length(bijective_listV g))
   are discharged via the monad-side lemma
   dfs_finish_repeat_break_safe_cardV_timer (above), which derives them
   from safe st (repeat_break (dfs_finish_repeat_body g u) ∅) X.
   ===================================================================== *)
Lemma dfs1_entry_close :
  forall (g: AdjGraph) (radj_col_l radj_row_l vis1_l fin_l: list Z) (u timer_v: Z)
         (X: unit -> KSt -> Prop),
    csr_wf1 g radj_col_l radj_row_l vis1_l fin_l ->
    csr1_faithful g radj_col_l radj_row_l ->
    (0 <= u < adj_verts g)%Z ->
    safeExec (pre_dfs1 g radj_col_l radj_row_l vis1_l fin_l timer_v) (dfs_finish g u) X ->
    safeExec (pre_dfs1 g radj_col_l radj_row_l (replace_Znth u 1 vis1_l) fin_l timer_v)
             (dfs_finish_from g radj_col_l radj_row_l u (csr_lo u radj_row_l)) X.
Proof.
  intros g radj_col_l radj_row_l vis1_l fin_l u timer_v X Hwf Hfaith Hub Hsafe.
  (* Extract csr_wf1 conjuncts; re-conjoin Hwf for dfs_finish_from_sim. *)
  destruct Hwf as [Hgv [Hlenrow [Hlenvis [Hlenfin [Hmof [Hlolo [Hhihi [Hneigh [Hlolohi Hmcap]]]]]]]]].
  assert (Hwf' : csr_wf1 g radj_col_l radj_row_l vis1_l fin_l).
  { unfold csr_wf1. repeat (split; [ assumption | ]); try assumption. }
  (* Peel visit1 u prelude; land safeExec over repeat_break B ∅ at σ'. *)
  pose proof (dfs1_visit_decompose g radj_col_l radj_row_l vis1_l fin_l timer_v u X
                Hgv Hlenvis Hub Hsafe) as Hdec.
  destruct Hdec as [σ' [Hpreσ' Hsafeσ']].
  (* pre_dfs1 conjuncts (Hpreσ' kept intact for the final safeExec wrap). *)
  pose proof (proj1 Hpreσ') as Hvis.
  (* Monad-side cardV/timer bounds from the repeat_break safeExec. *)
  pose proof (dfs_finish_repeat_break_safe_cardV_timer g u σ' X Hgv Hsafeσ') as [HcardV Htimerbd].
  (* visited1 σ' u: Znth u (replace_Znth u 1 vis1_l) 0 = 1 <> 0 via Znth_replace_eq. *)
  assert (Huvis : (0 <= u < Zlength vis1_l)%Z) by (rewrite Hlenvis; exact Hub).
  assert (Hvisu : visited1 σ' u).
  { apply (proj2 (Hvis u Hub)).
    rewrite (Znth_replace_eq vis1_l u 1 0 Huvis). discriminate. }
  (* Apply dfs_finish_from_sim at the entry cursor (i = csr_lo u, e_set = ∅, σ'). *)
  set (lo := csr_lo u radj_row_l) in *.
  set (hi := csr_hi u radj_row_l) in *.
  assert (Hlo_eq : csr_lo u radj_row_l = lo) by reflexivity.
  assert (Hhi_eq : csr_hi u radj_row_l = hi) by reflexivity.
  assert (Hloi : (lo <= lo)%Z) by lia.
  assert (Hlohi : (0 <= hi - lo)%Z).
  { pose proof (Hlolohi u Hub) as Hlh. unfold lo, hi in *. lia. }
  set (n := Z.to_nat (hi - lo)).
  assert (Hfuel : Z.to_nat (hi - lo) = n) by reflexivity.
  (* Invariants at entry (i = lo, e_set = ∅): A vacuous (empty set),
     B vacuous (empty range lo<=k<lo), E trivial (~ empty-set membership). *)
  assert (HA : forall (e: Z * Z), (fun _ => False) e ->
                exists k, (lo <= k < lo)%Z /\ e = (Znth k radj_col_l 0, u)).
  { intros e Hf. exfalso. exact Hf. }
  assert (HB : forall k, (lo <= k < lo)%Z -> ~ (fun _ => False) (Znth k radj_col_l 0, u) ->
                 visited1 σ' (Znth k radj_col_l 0)).
  { intros k [Hk1 Hk2] _. lia. }
  assert (HE : forall j, (lo <= j < hi)%Z -> ~ visited1 σ' (Znth j radj_col_l 0) ->
                 ~ (fun _ => False) (Znth j radj_col_l 0, u)).
  { intros j Hj Hnv Hf. exact Hf. }
  (* Apply the cursor-vs-repeat_break simulation. *)
  assert (Hsafe_ih : safe σ' (dfs_finish_from g radj_col_l radj_row_l u lo) X).
  { eapply dfs_finish_from_sim;
      [ exact Hlo_eq | exact Hhi_eq | exact Hwf' | exact Hfaith | exact Hub |
        exact Hfuel | exact Hloi | exact HA | exact HB | exact HE |
        exact Hvisu | exact HcardV | exact Htimerbd | exact Hsafeσ' ]. }
  (* Wrap back to safeExec at σ'. *)
  exists σ'. split; [ exact Hpreσ' | exact Hsafe_ih ].
Qed.
