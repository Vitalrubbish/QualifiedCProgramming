Require Import Coq.Lists.List.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Classes.EquivDec.
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

End TarjanSCC.
