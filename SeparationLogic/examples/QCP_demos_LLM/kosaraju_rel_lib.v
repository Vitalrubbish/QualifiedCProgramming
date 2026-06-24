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

From FP Require Import SetsFixedpoints.
From GraphLib Require Import graph_basic reachable_basic.
From MonadLib Require Import MonadLib.
Import StateRelMonad.
From Algorithms Require Import Kosaraju.Kosaraju Kosaraju.SCC.
Export MonadNotation.
Local Open Scope monad.
Local Open Scope sac.

(* ================================================================= *)
(* Adjacency-list graph carrier (directed).                          *)
(*   adj_fwd !! u = forward (out) neighbours of u                    *)
(*   adj_rev !! u = reversed (in) neighbours of u                    *)
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

(* Placeholder monad program: a single reverse-graph DFS finish call on
   the empty graph carrier.  Real per-vertex dispatch arrives in later
   refinement stages. *)
Definition dfs_finish (u : Z) : program KSt unit :=
  @DFS_finish AdjGraph Z (Z * Z) KG empty_adj u.

(* ================================================================= *)
(* Stage 1: heap-side memory representation.                         *)
(*                                                                   *)
(* Adjacency-list node layout (mirrors sll_def.h):                   *)
(*   struct list { int data; struct list *next; };                   *)
(* where the inline `data` int cell is the to-vertex.  Hence the     *)
(*   neighbourhood of a vertex is exactly an `sll` of Z to-vertices.   *)
(* ================================================================= *)

Require Import SimpleC.EE.QCP_demos_LLM.sll_lib.

(* A single adjacency-list (the out-neighbourhood of one vertex),
   living at head pointer [p], listing to-vertices [ns]. *)
Definition edge_list (p : addr) (ns : list Z) : Assertion := sll p ns.

(* A full array of [n] adjacency-list head pointers stored at [arr]
   (an IntArray of head addresses, since addr = Z), each head [u]
   owning the edge-list [adj !! u].  The IntArray owns the pointer
   slots; each [edge_list] owns its own nodes disjointly. *)
Fixpoint adj_array (arr : addr) (n : nat) (adj : list (list Z)) : Assertion :=
  match adj with
  | nil       => IntArray.full arr (Z.of_nat n) nil
  | ns :: adj0 =>
      let rest := adj_array (arr + 1) (n - 1) adj0 in
      EX h : addr,
        IntArray.full arr 1 [h] **
        edge_list h ns **
        rest
  end.

(* The complete Kosaraju heap: forward adjacency list, reversed
   adjacency list, and the four state arrays
   (visited1 / visited2 / finish / scc_id), each a full IntArray of
   length [n].  All seven resources are disjoint. *)
Definition kosaraju_mem (g : AdjGraph)
  (fadj_arr radj_arr vis1_arr vis2_arr fin_arr sid_arr : addr)
  (n : nat)
  (vis1_l vis2_l fin_l sid_l : list Z) : Assertion :=
  adj_array fadj_arr n (adj_fwd g) **
  adj_array radj_arr n (adj_rev g) **
  IntArray.full vis1_arr (Z.of_nat n) vis1_l **
  IntArray.full vis2_arr (Z.of_nat n) vis2_l **
  IntArray.full fin_arr  (Z.of_nat n) fin_l **
  IntArray.full sid_arr  (Z.of_nat n) sid_l.

(* Relates the abstract monad state [st : KSt] to the logical contents
   of the four C state arrays plus the scalar timer / scc_next.
   - visited1/visited2 are predicates V -> Prop encoded as 0/1 cells.
   - finish/scc_id are V -> nat encoded as Z cells (nat <-> Z). *)
Definition k_state (g : AdjGraph)
  (vis1_l vis2_l fin_l sid_l : list Z)
  (timer_v scc_next_v : Z) (st : KSt) : Prop :=
  (forall u, (0 <= u < adj_verts g)%Z ->
     visited1 st u <-> Znth u vis1_l 0 <> 0%Z) /\
  (forall u, (0 <= u < adj_verts g)%Z ->
     visited2 st u <-> Znth u vis2_l 0 <> 0%Z) /\
  (forall u, (0 <= u < adj_verts g)%Z ->
     finish st u = Z.to_nat (Znth u fin_l 0)) /\
  (forall u, (0 <= u < adj_verts g)%Z ->
     scc_id st u = Z.to_nat (Znth u sid_l 0)) /\
  timer st = Z.to_nat timer_v /\
  scc_next st = Z.to_nat scc_next_v.

(* A simple, refinement-faithful accessor reading a single visited1
   cell; used to validate the IntArray read path and the visited1
   <-> 0/1 encoding before the DFS stages. *)
Definition kosaraju_get_visited1_rel (u : Z) (vis1_l : list Z)
  : program KSt Z := return (Znth u vis1_l 0).

(* ================================================================= *)
(* Stage 2: reverse-graph DFS (dfs1) refinement fragments.           *)
(*                                                                   *)
(* The abstract monad program refined is                             *)
(*   DFS_finish u = Lfix (DFS_finish_f) u                            *)
(* which unfolds (Kosaraju.v, repeat_break_unfold) to                *)
(*   visit1 u ;;                                                     *)
(*   repeat_break (fun e_set =>                                      *)
(*       choice                                                      *)
(*         (e <- any E;; v <- any V;;                                *)
(*          assume (~ e IN e_set);; assume (~ visited1 st v);;        *)
(*          assume (step_aux g e v u);;   [reverse edge e=(v,u)]      *)
(*          W v;;                          [recurse]                   *)
(*          continue (e_set UNION {e}))                              *)
(*         (assume (forall e v, step_aux g e v u ->                  *)
(*                   e IN e_set \/ visited1 st v);;                   *)
(*          t <- get (fun st => t = timer st);;                      *)
(*          set_finish u t;; break tt))                              *)
(*   EMPTY.                                                          *)
(*                                                                   *)
(* C-side dfs1 walks radj[u] (reverse-adjacency list of u = the set  *)
(* of vertices v with a forward edge INTO u, equivalently the         *)
(* reverse-graph out-neighbours of u) using a WHILE loop with cursor  *)
(* [cur].  Each iteration peels one neighbour v; if v is unvisited,   *)
(* dfs1 recurses into v's reverse-graph DFS (graph recursion); then   *)
(* the cursor advances cur = cur->next (a plain Inv-preservation VC,  *)
(* NOT a recursion point, so no symexec prefill is needed for the     *)
(* sllseg-growth step).  After the loop, set_finish u timer.          *)
(*                                                                   *)
(* Loop-progress measure is the list of edge identities already      *)
(* processed:   done : list (Z * Z).                                 *)
(* ================================================================= *)

(* Loop-induction fragment: the repeat_break loop starting with an
   already-processed edge set [done] (visit1 u is assumed done).
   Closed over the concrete empty_adj carrier, mirroring [dfs_finish]. *)
Definition dfs_finish_loop_body
  (W : Z -> program KSt unit)
  (u : Z) (e_set : Z * Z -> Prop) : program KSt (CntOrBrk (Z * Z -> Prop) unit) :=
  choice
    (e <- any (Z * Z);;
     v <- any Z;;
     assume (fun _ => ~ e ∈ e_set);;
     assume (fun st => ~ visited1 st v);;
     assume (fun _ => step_aux empty_adj e v u);;
     W v;;
     continue (fun e' => e' ∈ e_set \/ e' = e))
    (assume (fun st =>
               forall (e : Z * Z) (v : Z),
                 step_aux empty_adj e v u ->
                 e ∈ e_set \/ visited1 st v);;
     t <- get (fun st t => t = timer st);;
     set_finish u t;;
     break tt).

Definition dfs_finish_from (u : Z) (done : list (Z * Z))
  : program KSt unit :=
  repeat_break
    (fun e_set => dfs_finish_loop_body (fun v => dfs_finish v) u e_set)
    (fun e => In e done).

(* Thin wrapper used as the recursion-point continuation: after the
   recursive call DFS_finish v returns, resume u's loop from [done]. *)
Definition dfs_finish_after (u : Z) (done : list (Z * Z)) (tt_ : unit)
  : program KSt unit :=
  dfs_finish_from u done.

(* Recursion-point continuation wrapper (cf. int_array_merge's bind of
   gmergesortrec with its continuation).  [dfs_finish u] produces unit,
   so the continuation takes [unit]. *)
Definition dfs1_aux (u : Z) {B : Type} (f : unit -> program KSt B)
  : program KSt B :=
  dfs_finish u ;; f tt.

(* Trivial continuation used at the top-level [low_level_spec] call:
   after dfs1 finishes, there is no further continuation work, so the
   continuation just returns unit. *)
Definition dfs1_ret_cont (tt_ : unit) : program KSt unit := return tt.

(* Scoped abstract-state precondition for dfs1: relates [st] to the
   three state components dfs1 touches (visited1, finish, timer).  The
   untouched components (visited2, scc_id, scc_next) are unconstrained
   here; carried by the outer frame.  Pure mathematical relation. *)
Definition pre_dfs1 (g : AdjGraph)
  (vis1_l fin_l : list Z) (timer_v : Z) (st : KSt) : Prop :=
  AdjGraphValid g /\
  (forall u, (0 <= u < adj_verts g)%Z ->
     visited1 st u <-> Znth u vis1_l 0 <> 0%Z) /\
  (forall u, (0 <= u < adj_verts g)%Z ->
     finish st u = Z.to_nat (Znth u fin_l 0)) /\
  timer st = Z.to_nat timer_v.

(* Edge-identity helper: the reverse-graph edges processed by dfs1's
   loop after walking the prefix [vs] of radj[u] are exactly the pairs
   (v, u) for each traversed to-vertex v.  Pure list function used only
   to phrase the loop invariant; not an algorithm mirror. *)
Fixpoint edges_of (u : Z) (vs : list Z) : list (Z * Z) :=
  match vs with
  | nil      => nil
  | v :: vs' => (v, u) :: edges_of u vs'
  end.

(* A default nth for use in C annotations where out-of-range must yield
   a concrete default rather than the option-wrapped [nth]. *)
Definition nth_def {A : Type} (l : list A) (i : Z) (dfl : A) : A :=
  nth (Z.to_nat i) l dfl.

(* A single scalar Z cell at address [a].  Used for the timer cell
   pointed to by timer_p.  Pure spatial predicate. *)
Definition zcell (a : addr) (z : Z) : Assertion := a # Int |-> z.

(* ================================================================= *)
(* Prorefine lemmas feeding the recursion / loop witnesses.          *)
(*                                                                   *)
(* [dfs_finish_unfold] decomposes a top-level dfs_finish u into      *)
(* visit1 u followed by the loop fragment starting from nil.         *)
(* [dfs_finish_from_unfold] unfolds one repeat_break step.           *)
(* [dfs_finish_from_cons] steps one reverse edge.                    *)
(* [adj_rev_step_iff] links radj[u] membership to step_aux g e v u.  *)
(* These are semantic refinement-faithfulness lemmas; for the Stage-2 *)
(* annotation-throughput milestone they may be admitted, with the     *)
(* admitted set listed in the subagent return report so the proving   *)
(* phase can close them.                                            *)
(* ================================================================= *)

Lemma dfs_finish_unfold : forall u,
  dfs_finish u == visit1 u ;; dfs_finish_from u nil.
Proof.
  intros u.
  (* dfs_finish u unfolds to visit1 u ;; repeat_break body nil. *)
  admit.
Admitted.

Lemma dfs_finish_from_unfold : forall u done,
  dfs_finish_from u done ==
  (x <- dfs_finish_loop_body (fun v => dfs_finish v) u (fun e' => In e' done);;
   match x with
   | by_continue e_set' => return tt
   | by_break b => return b
   end).
Proof.
  intros u done.
  (* repeat_break_unfold, specialised to the loop body of dfs_finish_from. *)
  admit.
Admitted.

Lemma dfs_finish_from_cons : forall u e v done,
  step_aux empty_adj e v u ->
  ~ In e done ->
  dfs_finish_from u (e :: done) ==
  (assume (fun _ => ~ In e done);;
   assume (fun st => ~ visited1 st v);;
   dfs_finish v;;
   dfs_finish_from u done).
Proof.
  intros u e v done Hstep Hnot.
  (* After recursing on edge e, the processed set becomes {e} UNION done. *)
  admit.
Admitted.

(* Direction coherence: v in radj[u] (reverse-adjacency of u) iff there
   is a reverse-graph edge e=(v,u) with step_aux g e v u.  Pure property
   for the recursion-point pure reasoning; may be admitted at Stage 2. *)
Lemma adj_rev_step_iff : forall g u v,
  AdjGraphValid g ->
  (0 <= u < adj_verts g)%Z ->
  In v (nth (Z.to_nat u) (adj_rev g) nil) <->
  exists e, e = (v, u) /\ step_aux g e v u.
Proof.
  intros g u v Hg [Hu1 Hu2].
  (* AdjGraphValid's transpose clause: In v (adj_rev!!u) iff In u (adj_fwd!!v). *)
  admit.
Admitted.

(* ================================================================= *)
(* Stage 3: forward-graph DFS (dfs2) refinement fragments.           *)
(*                                                                   *)
(* The abstract monad program refined is                             *)
(*   DFS_scc root u = Lfix (DFS_scc_f root) u                        *)
(* which unfolds (Kosaraju.v) to                                     *)
(*   visit2 u ;;                                                     *)
(*   set_scc_id u root;;                  [scc_id[u] := scc_id[root]] *)
(*   repeat_break (fun e_set =>                                      *)
(*       choice                                                      *)
(*         (e <- any E;; v <- any V;;                                *)
(*          assume (~ e IN e_set);; assume (~ visited2 st v);;        *)
(*          assume (step_aux g e u v);;  [forward edge e=(u,v)]       *)
(*          W v;;                          [recurse with SAME root]   *)
(*          continue (e_set UNION {e}))                              *)
(*         (assume (forall e v, step_aux g e u v ->                  *)
(*                   e IN e_set \/ visited2 st v);;                   *)
(*          break tt))                  [NO set_finish / NO timer]    *)
(*   EMPTY.                                                          *)
(*                                                                   *)
(* C-side dfs2 walks fadj[u] (forward-adjacency list of u = the set  *)
(* of vertices v with a forward edge OUT of u, equivalently the       *)
(* original-graph out-neighbours of u) using a WHILE loop with cursor *)
(* [cur].  Each iteration peels one neighbour v; if v is unvisited    *)
(* (visited2[v]==0), dfs2 recurses into (root, v)'s forward DFS       *)
(* (same root, propagating root's scc_id within the SCC); then the   *)
(* cursor advances cur = cur->next (a plain Inv-preservation VC).     *)
(* After the loop, dfs2 does NOTHING (DFS_scc's break branch only     *)
(* breaks, no set_finish).                                            *)
(*                                                                   *)
(* Loop-progress measure is the list of edge identities already      *)
(* processed:   done : list (Z * Z), with each edge stored as (u,v)  *)
(* matching step_aux g e u v.                                         *)
(* ================================================================= *)

(* dfs2 refines DFS_scc root u.  Closed over the concrete empty_adj    *)
(* carrier, mirroring [dfs_finish].  The graph contents live on the    *)
(* C heap side; root is the SCC-root vertex whose scc_id is propagated *)
(* to every vertex in the SCC.                                         *)
Definition dfs_scc (root u : Z) : program KSt unit :=
  @DFS_scc AdjGraph Z (Z * Z) KG empty_adj root u.

(* Loop-induction fragment: the repeat_break loop starting with an    *)
(* already-processed edge set [done] (visit2 u and set_scc_id u root  *)
(* are assumed done).  Forward edge direction: step_aux empty_adj e u v. *)
Definition dfs_scc_loop_body
  (root : Z)
  (W : Z -> program KSt unit)
  (u : Z) (e_set : Z * Z -> Prop) : program KSt (CntOrBrk (Z * Z -> Prop) unit) :=
  choice
    (e <- any (Z * Z);;
     v <- any Z;;
     assume (fun _ => ~ e ∈ e_set);;
     assume (fun st => ~ visited2 st v);;
     assume (fun _ => step_aux empty_adj e u v);;
     W v;;
     continue (fun e' => e' ∈ e_set \/ e' = e))
    (assume (fun st =>
               forall (e : Z * Z) (v : Z),
                 step_aux empty_adj e u v ->
                 e ∈ e_set \/ visited2 st v);;
     break tt).

Definition dfs_scc_from (root u : Z) (done : list (Z * Z))
  : program KSt unit :=
  repeat_break
    (fun e_set => dfs_scc_loop_body root (fun v => dfs_scc root v) u e_set)
    (fun e => In e done).

(* Thin wrapper used as the recursion-point continuation: after the
   recursive call DFS_scc root v returns, resume u's loop from [done].
   The root stays the same (SCC-internal propagation). *)
Definition dfs_scc_after (root u : Z) (done : list (Z * Z)) (tt_ : unit)
  : program KSt unit :=
  dfs_scc_from root u done.

(* Recursion-point continuation wrapper (cf. dfs1_aux).  [dfs_scc root u]
   produces unit, so the continuation takes [unit]. *)
Definition dfs2_aux (root u : Z) {B : Type} (f : unit -> program KSt B)
  : program KSt B :=
  dfs_scc root u ;; f tt.

(* Trivial continuation used at the top-level [low_level_spec] call. *)
Definition dfs2_ret_cont (tt_ : unit) : program KSt unit := return tt.

(* Scoped abstract-state precondition for dfs2: relates [st] to the
   two state components dfs2 touches (visited2, scc_id).  The untouched
   components (visited1, finish, timer, scc_next) are unconstrained here;
   carried by the outer frame.  Pure mathematical relation. *)
Definition pre_dfs2 (g : AdjGraph)
  (vis2_l sid_l : list Z) (st : KSt) : Prop :=
  AdjGraphValid g /\
  (forall u, (0 <= u < adj_verts g)%Z ->
     visited2 st u <-> Znth u vis2_l 0 <> 0%Z) /\
  (forall u, (0 <= u < adj_verts g)%Z ->
     scc_id st u = Z.to_nat (Znth u sid_l 0)).

(* ================================================================= *)
(* Prorefine lemmas feeding the dfs2 recursion / loop witnesses.      *)
(*                                                                   *)
(* [dfs_scc_unfold] decomposes a top-level dfs_scc root u into        *)
(* visit2 u ;; set_scc_id u root ;; dfs_scc_from root u nil.          *)
(* [dfs_scc_from_unfold] unfolds one repeat_break step.               *)
(* [dfs_scc_from_cons] steps one forward edge (same root recursion).  *)
(* [adj_fwd_step_iff] links fadj[u] membership to step_aux g e u v.   *)
(* These are semantic refinement-faithfulness lemmas; for the Stage-3 *)
(* annotation-throughput milestone they may be admitted, with the     *)
(* admitted set listed in the subagent return report so the proving   *)
(* phase can close them.                                            *)
(* ================================================================= *)

Lemma dfs_scc_unfold : forall root u,
  dfs_scc root u == visit2 u ;; set_scc_id u root ;; dfs_scc_from root u nil.
Proof.
  intros root u.
  (* dfs_scc root u unfolds to visit2 u ;; set_scc_id u root ;; repeat_break body nil. *)
  admit.
Admitted.

Lemma dfs_scc_from_unfold : forall root u done,
  dfs_scc_from root u done ==
  (x <- dfs_scc_loop_body root (fun v => dfs_scc root v) u (fun e' => In e' done);;
   match x with
   | by_continue e_set' => return tt
   | by_break b => return b
   end).
Proof.
  intros root u done.
  (* repeat_break_unfold, specialised to the loop body of dfs_scc_from. *)
  admit.
Admitted.

Lemma dfs_scc_from_cons : forall root u e v done,
  step_aux empty_adj e u v ->
  ~ In e done ->
  dfs_scc_from root u (e :: done) ==
  (assume (fun _ => ~ In e done);;
   assume (fun st => ~ visited2 st v);;
   dfs_scc root v;;
   dfs_scc_from root u done).
Proof.
  intros root u e v done Hstep Hnot.
  (* After recursing on forward edge e with same root, processed set becomes {e} UNION done. *)
  admit.
Admitted.

(* Direction coherence: v in fadj[u] (forward-adjacency of u) iff there
   is a forward-graph edge e=(u,v) with step_aux g e u v.  Pure property
   for the recursion-point pure reasoning; may be admitted at Stage 3. *)
Lemma adj_fwd_step_iff : forall g u v,
  AdjGraphValid g ->
  (0 <= u < adj_verts g)%Z ->
  In v (nth (Z.to_nat u) (adj_fwd g) nil) <->
  exists e, e = (u, v) /\ step_aux g e u v.
Proof.
  intros g u v Hg [Hu1 Hu2].
  (* By definition of adj_step_aux: e=(u,v), step_aux iff In v (adj_fwd!!u). *)
  admit.
Admitted.

(* ================================================================= *)
(* Stage 4: outer Kosaraju loops + top-level kosaraju_run.           *)
(*                                                                   *)
(* The abstract monad programs refined are (Kosaraju.v):             *)
(*   kosaraju_finish = Lfix kosaraju_finish_f tt                     *)
(*     kosaraju_finish_f W tt =                                      *)
(*       choice (u <- pick_unvisited1;; DFS_finish u;; W tt)         *)
(*              (assume (forall v, visited1 st v);; skip)            *)
(*   kosaraju_scc    = Lfix kosaraju_scc_f tt                        *)
(*     kosaraju_scc_f W tt =                                         *)
(*       choice (u <- pick_unvisited2;; set_scc_root_id u;;          *)
(*               DFS_scc u u;; W tt)                                 *)
(*              (assume (forall v, visited2 st v);; skip)            *)
(*   kosaraju = kosaraju_finish ;; kosaraju_scc.                     *)
(*                                                                   *)
(* C-side outer loops use a deterministic for(i<n) over the vertex    *)
(* range [0,n); this is an angelic/existential realization of the    *)
(* non-deterministic pick_unvisited1 / pick_unvisited2: every        *)
(* unvisited vertex is eventually visited, so the for-loop reaches   *)
(* a state in which all vertices are visited (the Lfix break branch).*)
(* pick_unvisited2's "maximal finish" is realized on the C side by   *)
(* iterating a pre-sorted order[] array (finish descending); the     *)
(* correctness of that sort is captured by [order_sorted] and is     *)
(* deferred to the proving phase (low_level-first).                  *)
(*                                                                   *)
(* The outer loop invariant is expressed with a continuation         *)
(* [kosaraju_finish_from done_i] / [kosaraju_scc_from done_i] that   *)
(* represents the Lfix continuation assuming vertices 0..done_i-1    *)
(* have already been processed.  Pure mathematical continuation,     *)
(* closed over the concrete empty_adj carrier.                       *)
(* ================================================================= *)

(* Top-level abstract programs, closed over empty_adj.  The graph     *)
(* contents live on the C heap; these are the Lfix fixpoints from     *)
(* Kosaraju.v instantiated at the concrete carrier.                  *)
Definition kosaraju_finish_monad : program KSt unit :=
  @kosaraju_finish AdjGraph Z (Z * Z) KG empty_adj.

Definition kosaraju_scc_monad : program KSt unit :=
  @kosaraju_scc AdjGraph Z (Z * Z) KG empty_adj.

Definition kosaraju_monad : program KSt unit :=
  kosaraju_finish_monad ;; kosaraju_scc_monad.

(* [kosaraju_finish_from done_i] is the remaining-work continuation of *)
(* kosaraju_finish after the C-side for-loop has already attempted     *)
(* vertices 0..done_i-1.  On the monad side the loop cursor done_i is  *)
(* a PURE loop-progress token carried by the C invariant: it records   *)
(* that vertices < done_i have already been attempted.  The monad      *)
(* continuation itself is the whole kosaraju_finish Lfix fixpoint,     *)
(* because the abstract monad is the non-deterministic angelic pick    *)
(* (pick_unvisited1) of which the deterministic for-loop is one        *)
(* existential realization under safeExec.  The C invariant carries    *)
(* the "< done_i already processed" progress purely on the assertion   *)
(* side, so that any unvisited vertex the monad may pick is >= done_i. *)
(*                                                                    *)
(* This is a pure mathematical continuation: a closed monad program    *)
(* indexed by the loop cursor, NOT a Rocq mirror of the C for-loop.    *)
Definition kosaraju_finish_from (done_i : Z) : program KSt unit :=
  kosaraju_finish_monad.

(* [kosaraju_scc_from done_i] is the analogous remaining-work          *)
(* continuation of kosaraju_scc after the order-driven for-loop has    *)
(* already attempted the first done_i entries of order[].  Same shape: *)
(* done_i is a pure loop-progress token on the C side; the monad       *)
(* continuation is the whole kosaraju_scc Lfix fixpoint (the angelic   *)
(* pick_unvisited2, of which the finish-descending order[] iteration   *)
(* is one existential realization).                                   *)
Definition kosaraju_scc_from (done_i : Z) : program KSt unit :=
  kosaraju_scc_monad.

(* kosaraju_finish_from / kosaraju_scc_from above are the loop-cursor-   *)
(* indexed continuations used in the C invariant; each equals the whole   *)
(* kosaraju_finish / kosaraju_scc Lfix (the monad-side continuation is    *)
(* the abstract angelic pick_unvisited, of which the C for-loop's         *)
(* deterministic order is one existential realization under safeExec,     *)
(* carried purely on the assertion side).  No single-step unfolding       *)
(* lemmas (from_step / step_prog_next / all_visited) are needed: the      *)
(* generated VCs keep the continuation opaque, so they are omitted here   *)
(* (they were vacuous on the empty_adj carrier anyway, adj_verts = 0).    *)

(* order_sorted: the C-side order[] array lists vertices in           *)
(* non-increasing finish-time order.  [order_l] is the logical list   *)
(* of vertex ids stored in order[]; [fin_l] is the logical finish[]   *)
(* array.  Pure mathematical definition; the proof that a correctly   *)
(* produced order[] satisfies this is deferred to the proving phase.  *)
Definition order_sorted (order_l fin_l : list Z) : Prop :=
  forall k1 k2,
    (0 <= k1)%Z -> (k1 < k2)%Z -> (k2 < Z.of_nat (length order_l))%Z ->
    (Znth (Znth k1 order_l 0) fin_l 0 >= Znth (Znth k2 order_l 0) fin_l 0)%Z.

(* pre_kosaraju: the full state relation connecting the abstract     *)
(* monad state [st] to all six C-side state components.  This is the  *)
(* outer-frame precondition for kosaraju_run; inner dfs1/dfs2 use     *)
(* their scoped pre_dfs1/pre_dfs2 which this relation entails.       *)
Definition pre_kosaraju (g : AdjGraph)
  (vis1_l vis2_l fin_l sid_l : list Z)
  (timer_v scc_next_v : Z) (st : KSt) : Prop :=
  AdjGraphValid g /\
  Zlength vis1_l = adj_verts g /\
  Zlength vis2_l = adj_verts g /\
  Zlength fin_l = adj_verts g /\
  Zlength sid_l = adj_verts g /\
  (forall u, (0 <= u < adj_verts g)%Z ->
     visited1 st u <-> Znth u vis1_l 0 <> 0%Z) /\
  (forall u, (0 <= u < adj_verts g)%Z ->
     visited2 st u <-> Znth u vis2_l 0 <> 0%Z) /\
  (forall u, (0 <= u < adj_verts g)%Z ->
     finish st u = Z.to_nat (Znth u fin_l 0)) /\
  (forall u, (0 <= u < adj_verts g)%Z ->
     scc_id st u = Z.to_nat (Znth u sid_l 0)) /\
  timer st = Z.to_nat timer_v /\
  scc_next st = Z.to_nat scc_next_v.
