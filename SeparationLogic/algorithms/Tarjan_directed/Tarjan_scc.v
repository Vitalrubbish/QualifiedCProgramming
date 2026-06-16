Require Import Coq.Lists.List.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Classes.EquivDec.
Require Import Coq.Relations.Relations.
Require Import SetsClass.SetsClass.
From MonadLib.StateRelMonad Require Import StateRelBasic StateRelHoare FixpointLib.
From RecordUpdate Require Import RecordUpdate.
From GraphLib Require Import graph_basic Syntax.
From GraphLib.examples Require Import tarjan.
From Algorithms.Tarjan_directed Require Import SCC_basic.

Import SetsNotation.
Import MonadNotation.
Local Open Scope sets.
Local Open Scope monad.

Section TarjanSCC.

  Context {V E: Type}
          `{EqDec V eq}
          (g: OriginalGraphType V E)
          `{OriginalGraph_gvalid g}.

  (* ================================================================ *)
  (* State Record                                                     *)
  (* ================================================================ *)

  Record SCCSt: Type := mkSCCSt {
    visited : V -> Prop;
    timer   : nat;
    fa      : V -> V;
    dfn     : V -> nat;
    low     : V -> nat;
    stack   : list V;
    sccs    : list (V -> Prop);
  }.

  Instance: Settable SCCSt := settable! mkSCCSt
    <visited; timer; fa; dfn; low; stack; sccs>.

  (* ================================================================ *)
  (* Initial State                                                    *)
  (* ================================================================ *)

  Definition initSt: SCCSt :=
    mkSCCSt (fun _ => False) 0 (fun v => v) (fun _ => 0) (fun _ => 0) nil nil.

  (* ================================================================ *)
  (* stack_split_at — split stack at target vertex u (inclusive)      *)
  (* ================================================================ *)

  Fixpoint stack_split_at (stk: list V) (u: V): list V * list V :=
    match stk with
    | nil => (nil, nil)
    | x :: xs =>
        if equiv_decb x u
        then (x :: nil, xs)
        else let (popped, rest) := stack_split_at xs u in
             (x :: popped, rest)
    end.

  (* ================================================================ *)
  (* pop_scc_state — pure function to pop an SCC from the stack       *)
  (* ================================================================ *)

  Definition pop_scc_state (s: SCCSt) (u: V): SCCSt :=
    let '(popped, rest) := stack_split_at (stack s) u in
    s <| stack ::= fun _ => rest |>
      <| sccs ::= fun sccs0 => (fun v => In v popped) :: sccs0 |>.

  (* ================================================================ *)
  (* Primitive Operations                                             *)
  (* ================================================================ *)

  Definition visit (v: V): program SCCSt unit :=
    update' (fun s => s <| visited ::= fun x => x ∪ [v] |>).

  Definition set_dfn (v: V) (n: nat): program SCCSt unit :=
    update' (fun s => s <| dfn ::= fun dfn0 x => if equiv_decb x v then n else dfn0 x |>).

  Definition set_low (v: V) (n: nat): program SCCSt unit :=
    update' (fun s => s <| low ::= fun low0 x => if equiv_decb x v then n else low0 x |>).

  Definition set_fa (v: V) (p: V): program SCCSt unit :=
    update' (fun s => s <| fa ::= fun fa0 x => if equiv_decb x v then p else fa0 x |>).

  Definition incr_timer: program SCCSt unit :=
    update' (fun s => s <| timer ::= fun t => S t |>).

  Definition push_stack (v: V): program SCCSt unit :=
    update' (fun s => s <| stack ::= fun stk => v :: stk |>).

  Definition update_low (u: V) (n: nat): program SCCSt unit :=
    lu <- get' (fun s => low s u);;
    If (fun s => n < low s u) (set_low u n).

  Definition pop_scc (u: V): program SCCSt unit :=
    update' (fun s => pop_scc_state s u).

  Ltac unfold_op :=
    unfold visit, set_dfn, set_low, set_fa, incr_timer,
           push_stack, update_low, pop_scc.

  (* ================================================================ *)
  (* Main Program                                                     *)
  (* ================================================================ *)

  Definition preloop (u: V): program SCCSt unit :=
    t <- get (fun s t => t = s.(timer));;
    set_dfn u t;;
    set_low u t;;
    incr_timer;;
    push_stack u;;
    visit u.

  Definition process_edge (u: V) (W: V -> program SCCSt unit) (v: V): program SCCSt unit :=
    if_else (fun s => ~ v ∈ visited s)
      (* Tree edge: v is unvisited *)
      (set_fa v u;; W v;;
       lv <- get' (fun s => low s v);;
       update_low u lv)
      (* v is already visited — check if it's still in the stack *)
      (If (fun s => In v (stack s))
         (dv <- get' (fun s => dfn s v);;
          update_low u dv)).

  Definition tarjan_scc_f (W: V -> program SCCSt unit) (u: V): program SCCSt unit :=
    preloop u;;
    forset (fun v => dg_step g u v) (process_edge u W);;
    If (fun s => low s u = dfn s u) (pop_scc u).

  Definition tarjan_scc (u: V): program SCCSt unit :=
    Lfix tarjan_scc_f u.

  (* ================================================================ *)
  (* DFS Tree Construction                                            *)
  (* ================================================================ *)

  (** [state_to_dfs_tree s root] constructs the DFS tree from the algorithm
      state [s].  The [root] parameter is the DFS traversal root vertex; it
      is not used in the tree structure itself but is required by the
      [RootedTree] Type Class instance (proved in a separate file) which
      takes [root] as the tree root. *)
  Definition state_to_dfs_tree (s: SCCSt) (root: V): OriginalGraphType V E :=
    {|
      original_vvalid   := fun v => v ∈ visited s;
      original_step     := fun e =>
        exists v, v ∈ visited s /\ fa s v <> v /\
                  original_step_fst g e = fa s v /\
                  original_step_snd g e = v;
      original_step_fst := original_step_fst g;
      original_step_snd := original_step_snd g;
      original_listV    := original_listV g;
    |}.

  (** [set_fa_state s v p] is the pure functional version of [set_fa].
      It returns a new state where [fa] maps [v] to [p] and leaves all
      other [fa] entries unchanged.  This is the same update as the
      monadic [set_fa] but exposed as a pure function for use in
      structural lemmas about [state_to_dfs_tree]. *)
  Definition set_fa_state (s: SCCSt) (v p: V): SCCSt :=
    s <| fa ::= fun fa0 x => if equiv_decb x v then p else fa0 x |>.

  (* ================================================================ *)
  (* Monotonicity                                                     *)
  (* ================================================================ *)

  (** [process_edge_mono_cont]: the edge-processing step is mono_cont
      in the recursive body parameter [W]. *)
  Lemma process_edge_mono_cont (u v: V):
    mono_cont (fun (W: V -> program SCCSt unit) => process_edge u W v).
  Proof.
    unfold process_edge, if_else.
    unfold_op.
    mono_cont_auto.
  Qed.

  (** [forset_body_mono_cont]: the body of [forset_f] is mono_cont in
      the external parameter [W], for each fixed recursive self [W0]
      and universe [universe']. *)
  Lemma forset_body_mono_cont (u: V)
        (W0: (V -> Prop) -> program SCCSt unit) (universe': V -> Prop):
    mono_cont (fun (W: V -> program SCCSt unit) =>
      choice
        (a <- get (fun (_: SCCSt) (a: V) => a ∈ universe');;
         process_edge u W a;;
         W0 (fun x => x ∈ universe' /\ x <> a))
        (assume!! (universe' == ∅);; skip)).
  Proof.
    apply mono_cont_choice.
    - apply mono_cont_bind.
      + apply mono_cont_const.
      + intros a.
        apply mono_cont_bind.
        * apply process_edge_mono_cont.
        * intros _. apply mono_cont_const.
    - apply mono_cont_const.
  Qed.

  (** [mono_cont_apply]: [fun W => W s] is mono_cont for a constant
      set argument [s].  This is a concrete instantiation needed by
      the [forset_f] proof. *)
  Lemma mono_cont_apply (s: V -> Prop):
    mono_cont (fun (W: (V -> Prop) -> program SCCSt unit) => W s).
  Proof.
    split.
    - red. intros W1 W2 Hincl.
      red. revert Hincl.
      cbv [Sets.included Sets.lift_included].
      intros Hincl. apply Hincl.
    - red. intros T HmonoT.
      red.
      cbv [Sets.equiv Sets.lift_equiv Sets.included Sets.lift_included
             Sets.lift_indexed_union Sets.indexed_union].
      split; intro; apply H.
  Qed.

  (** [forset_f_mono_cont_body]: when [body : V -> program SCCSt unit] is
      a constant (does not depend on an external parameter), [forset_f body]
      is mono_cont.  This covers the inner [forset_f] logic without the
      extra [W] parameter. *)
  Lemma forset_f_mono_cont_body (body: V -> program SCCSt unit):
    mono_cont (forset_f body).
  Proof.
    unfold forset_f.
    apply mono_cont_intro; intro W0.
    (* Goal: mono_cont (fun W : ((V -> Prop) -> program SCCSt unit) =>
               choice (a <- get ... ;; body a ;; W (...)) (assume!! ... ;; skip)) *)
    apply mono_cont_choice.
    - apply mono_cont_bind.
      + apply mono_cont_const.
      + intros a.
        apply mono_cont_bind.
        * apply mono_cont_const.
        * intros _. apply mono_cont_apply.
    - apply mono_cont_const.
  Qed.

  Lemma tarjan_scc_f_mono_cont: mono_cont tarjan_scc_f.
  Proof.
    unfold tarjan_scc_f.
    apply mono_cont_intro; intro u.
    apply mono_cont_bind.
    { apply mono_cont_const. }
    intros _.
    apply mono_cont_bind.
    { unfold forset.
      set (univ := fun v : V => dg_step g u v).
      set (F := fun (W: V -> program SCCSt unit) =>
        forset_f (process_edge u W)).
      assert (Hmono_Lfix : mono_cont (fun W => Lfix (F W))).
      { apply mono_cont_Lfix.
        - intro W_fixed. subst F. apply forset_f_mono_cont_body.
        - intro b. subst F.
          unfold forset_f.
          split.
          + (* mono part: pointwise in universe' *)
            intros W1 W2 Hincl universe'.
            pose proof (forset_body_mono_cont u b universe') as Hfb.
            destruct Hfb as [Hfb_mono _].
            red in Hfb_mono.
            apply Hfb_mono; assumption.
          + (* continuous part: sup commutes pointwise *)
            intros T HmonoT universe'.
            pose proof (forset_body_mono_cont u b universe') as Hfb.
            destruct Hfb as [_ Hfb_cont].
            red in Hfb_cont.
            exact (Hfb_cont T HmonoT). }
      destruct Hmono_Lfix as [Hmono_Lfix Hcont_Lfix].
      split.
      + intros W1 W2 Hincl.
        exact (Hmono_Lfix W1 W2 Hincl univ).
      + intros T HmonoT.
        cbv [Sets.lift_indexed_union].
        exact (Hcont_Lfix T HmonoT univ). }
    intros _.
    apply mono_cont_const.
  Qed.

  Lemma tarjan_scc_unfold (u: V):
    tarjan_scc u == tarjan_scc_f tarjan_scc u.
  Proof.
    unfold tarjan_scc.
    assert (Hfix: Lfix tarjan_scc_f == tarjan_scc_f (Lfix tarjan_scc_f)).
    { apply Lfix_fixpoint'. apply tarjan_scc_f_mono_cont. }
    apply (Hfix u).
  Qed.

  (* ================================================================ *)
  (* Outer Loop — tarjan_scc_all                                      *)
  (* ================================================================ *)

  Definition tarjan_scc_all: program SCCSt unit :=
    forset (fun v => original_vvalid g v)
           (fun v => If (fun s => ~ v ∈ visited s) (tarjan_scc v)).

  (* ================================================================ *)
  (* DFS Tree — Structural Lemmas                                    *)
  (* ================================================================ *)

  (** [state_to_dfs_tree_vvalid]: The vertex set of the DFS tree is
      exactly the [visited] set of the algorithm state. *)
  Lemma state_to_dfs_tree_vvalid (s: SCCSt) (root v: V):
    original_vvalid (state_to_dfs_tree s root) v <-> v ∈ visited s.
  Proof.
    unfold state_to_dfs_tree, original_vvalid. reflexivity.
  Qed.

  (** [state_to_dfs_tree_step_char]: Forward characterization of
      directed edges in the DFS tree.  If the tree has an edge
      [x → y], then [fa s y = x], [fa s y ≠ y] (the [fa] field
      was actually assigned), and [y] is visited.

      The converse direction requires an additional edge-existence
      condition in the original graph [g]; see
      [state_to_dfs_tree_step_char_backward]. *)
  Lemma state_to_dfs_tree_step_char (s: SCCSt) (root x y: V):
    dg_step (state_to_dfs_tree s root) x y ->
    fa s y = x /\ fa s y <> y /\ y ∈ visited s.
  Proof.
    unfold dg_step.
    intros [e [Hstep [Hfst_eq Hsnd_eq]]].
    unfold original_step in Hstep.
    unfold state_to_dfs_tree in Hfst_eq, Hsnd_eq.
    simpl in Hfst_eq, Hsnd_eq.
    unfold state_to_dfs_tree in Hstep.
    simpl in Hstep.
    destruct Hstep as [v [Hvis [Hfa_ne [Hfst_fa Hsnd_v]]]].
    rewrite Hsnd_v in Hsnd_eq. (* Hsnd_eq: v = y *)
    rewrite Hfst_fa in Hfst_eq. (* Hfst_eq: fa s v = x *)
    rewrite <- Hsnd_eq.
    split; [exact Hfst_eq | split; [exact Hfa_ne | exact Hvis]].
  Qed.

  (** [state_to_dfs_tree_step_char_backward]: The converse direction
      of the edge characterization, requiring that a corresponding
      edge exists in the original graph [g].  This condition holds
      in reachable algorithm states because [fa s y = x] can only
      be established by [set_fa] in the tree-edge branch of
      [process_edge], which is guarded by [dg_step g x y]. *)
  Lemma state_to_dfs_tree_step_char_backward (s: SCCSt) (root x y: V):
    dg_step g x y ->
    fa s y = x -> fa s y <> y -> y ∈ visited s ->
    dg_step (state_to_dfs_tree s root) x y.
  Proof.
    intros Hstep_g Hfa_eq Hfa_ne Hvis.
    destruct Hstep_g as [e [Horig_step [Hfst_eq Hsnd_eq]]].
    unfold dg_step.
    exists e. split.
    - unfold original_step at 1.
      exists y. split; [exact Hvis | split; [exact Hfa_ne |]].
      rewrite Hfst_eq, Hsnd_eq.
      rewrite Hfa_eq. split; reflexivity.
    - split; [exact Hfst_eq | exact Hsnd_eq].
  Qed.

  (** [state_to_dfs_tree_step_fa]: If [v] is visited, [fa s v ≠ v],
      and the original graph has an edge from [fa s v] to [v], then
      there is a tree edge from [fa s v] to [v] in the DFS tree. *)
  Lemma state_to_dfs_tree_step_fa (s: SCCSt) (root v: V):
    dg_step g (fa s v) v ->
    v ∈ visited s -> fa s v <> v ->
    dg_step (state_to_dfs_tree s root) (fa s v) v.
  Proof.
    intros Hstep_g Hvis Hfa_ne.
    eapply state_to_dfs_tree_step_char_backward;
      eauto.
  Qed.

  (** [state_to_dfs_tree_dg_reachable_refl]: Every visited vertex is
      trivially reachable from itself in the DFS tree (reflexivity of
      [clos_refl_trans]). *)
  Lemma state_to_dfs_tree_dg_reachable_refl (s: SCCSt) (root v: V):
    v ∈ visited s ->
    dg_reachable (state_to_dfs_tree s root) v v.
  Proof.
    intros Hvis.
    apply rt_refl.
  Qed.

  (** [state_to_dfs_tree_root_visited]: If [root] is visited, then
      [root] is a valid vertex of the DFS tree. *)
  Lemma state_to_dfs_tree_root_visited (s: SCCSt) (root: V):
    root ∈ visited s ->
    original_vvalid (state_to_dfs_tree s root) root.
  Proof.
    intros Hvis.
    apply state_to_dfs_tree_vvalid. exact Hvis.
  Qed.

  (** [state_to_dfs_tree_no_self_loop]: The DFS tree has no self-loops.
      This follows from the [fa s v ≠ v] condition in the tree edge
      definition. *)
  Lemma state_to_dfs_tree_no_self_loop (s: SCCSt) (root v: V):
    ~ dg_step (state_to_dfs_tree s root) v v.
  Proof.
    intros Hstep.
    apply state_to_dfs_tree_step_char in Hstep.
    destruct Hstep as [Hfa_eq [Hfa_ne _]].
    apply Hfa_ne. exact Hfa_eq.
  Qed.

  (* ================================================================ *)
  (* DFS Tree — set_fa Preservation Lemmas                           *)
  (* ================================================================ *)

  (** [set_fa_preserves_tree_vvalid]: [set_fa] does not change the
      [visited] set, so the vertex set of the DFS tree is unchanged. *)
  Lemma set_fa_preserves_tree_vvalid (s: SCCSt) (root v p: V):
    original_vvalid (state_to_dfs_tree s root) v ->
    original_vvalid (state_to_dfs_tree (set_fa_state s v p) root) v.
  Proof.
    unfold state_to_dfs_tree, set_fa_state, original_vvalid.
    simpl. auto.
  Qed.

  (** [set_fa_preserves_tree_edges]: When [w ≠ v], an existing tree
      edge [x → w] is preserved after [set_fa_state s v p].  The
      proof reuses the same edge witness [e] extracted from the
      original tree [dg_step] (no additional [dg_step g] condition
      is needed because we are not creating a new edge, just
      checking that the existing [e] still satisfies the tree-edge
      definition after the [fa] update of a different vertex [v]). *)
  Lemma set_fa_preserves_tree_edges (s: SCCSt) (root v x w p: V):
    w <> v ->
    dg_step (state_to_dfs_tree s root) x w ->
    dg_step (state_to_dfs_tree (set_fa_state s v p) root) x w.
  Proof.
    intros Hneq Hstep.
    unfold dg_step in Hstep.
    destruct Hstep as [e [Hstep_tree [Hfst_eq Hsnd_eq]]].
    unfold original_step in Hstep_tree.
    unfold state_to_dfs_tree in Hfst_eq, Hsnd_eq, Hstep_tree.
    simpl in Hfst_eq, Hsnd_eq, Hstep_tree.
    destruct Hstep_tree as [u [Hvis [Hfa_ne [Hfst_fa Hsnd_u]]]].
    rewrite Hsnd_u in Hsnd_eq. (* Hsnd_eq: u = w *)
    rewrite Hfst_fa in Hfst_eq. (* Hfst_eq: fa s u = x *)
    (* From Hneq and Hsnd_eq we get u <> v *)
    assert (Huneqv: u <> v).
    { intros Heq. apply Hneq. rewrite <- Heq. rewrite Hsnd_eq. reflexivity. }
    (* Rewrite the goal to use u instead of w, and fa s u instead of x *)
    rewrite <- Hsnd_eq.
    rewrite <- Hfst_eq.
    (* Goal: dg_step (state_to_dfs_tree (set_fa_state s v p) root) (fa s u) u *)
    unfold dg_step.
    exists e. split.
    - unfold state_to_dfs_tree, set_fa_state, original_step. simpl.
      exists u. split; [exact Hvis | split].
      + unfold equiv_decb. destruct (equiv_dec u v) as [Heq | _].
        { exfalso; apply Huneqv; exact Heq. }
        exact Hfa_ne.
      + split.
        * unfold equiv_decb. destruct (equiv_dec u v) as [Heq | _].
          { exfalso; apply Huneqv; exact Heq. }
          exact Hfst_fa.
        * exact Hsnd_u.
    - unfold state_to_dfs_tree, set_fa_state. simpl.
      split.
      + unfold equiv_decb. destruct (equiv_dec u v) as [Heq | _].
        { exfalso; apply Huneqv; exact Heq. }
        exact Hfst_fa.
      + exact Hsnd_u.
  Qed.

  (** [set_fa_adds_tree_edge]: After [set_fa_state s v p] with [p ≠ v]
      and [v ∈ visited s], the DFS tree gains a new edge [p → v],
      provided that such an edge exists in the original graph [g].

      In the algorithm, this edge-creation happens in the tree-edge
      branch of [process_edge]: [set_fa v u] is executed when the
      original graph has edge [u → v] ([dg_step g u v]), and [v] is
      unvisited.  The [v ∈ visited s] condition here reflects the
      state *after* [visit v] (inside the recursive [tarjan_scc v]
      call), at which point the tree edge becomes visible. *)
  Lemma set_fa_adds_tree_edge (s: SCCSt) (root v p: V):
    dg_step g p v ->
    p <> v -> v ∈ visited s ->
    dg_step (state_to_dfs_tree (set_fa_state s v p) root) p v.
  Proof.
    intros Hstep_g Hneq Hvis.
    unfold set_fa_state, state_to_dfs_tree.
    destruct Hstep_g as [e [Horig_step [Hfst_eq Hsnd_eq]]].
    unfold dg_step.
    exists e. split.
    - unfold original_step. simpl.
      exists v. split; [exact Hvis | split].
      + (* fa (set_fa_state s v p) v <> v *)
        simpl. unfold equiv_decb.
        destruct (equiv_dec v v) as [Heq | Hneq'].
        2: { exfalso; apply Hneq'; reflexivity. }
        exact Hneq.
      + split.
        * (* step_fst g e = fa (set_fa_state s v p) v *)
          simpl. unfold equiv_decb.
          destruct (equiv_dec v v) as [Heq | Hneq'].
          2: { exfalso; apply Hneq'; reflexivity. }
          rewrite Hfst_eq. reflexivity.
        * (* step_snd g e = v *)
          exact Hsnd_eq.
    - split; [exact Hfst_eq | exact Hsnd_eq].
  Qed.

End TarjanSCC.
