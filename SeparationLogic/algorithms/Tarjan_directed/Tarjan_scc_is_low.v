Require Import Coq.Classes.EquivDec.
Require Import Coq.Lists.List.
Require Import SetsClass.SetsClass.
From MonadLib.StateRelMonad Require Import StateRelBasic StateRelHoare FixpointLib.
From GraphLib Require Import graph_basic Syntax.
From GraphLib.examples Require Import tarjan.
From Algorithms.Tarjan_directed Require Import
  SCC_basic Tarjan_scc Tarjan_scc_basics Tarjan_scc_is_dfn
  Tarjan_scc_low_defs Tarjan_scc_low_pure Tarjan_scc_low_primitives.

Import SetsNotation.
Import MonadNotation.
Local Open Scope sets.
Local Open Scope monad.

Section IS_LOW.

  Context {V E: Type}
          `{EqDec V eq}
          (g: OriginalGraphType V E)
          `{OriginalGraph_gvalid g}
          (root: V)
          (g_vvalid_root: original_vvalid g root).

  (* ================================================================ *)
  (* Independent recursive frames                                    *)
  (* ================================================================ *)

  Definition Q_fa_stable (u: V) (s0: @SCCSt V) (_: unit) (s: @SCCSt V): Prop :=
    (forall w, w ∈ visited s0 -> w ∈ visited s) /\
    (forall w, w ∈ visited s0 -> fa s w = fa s0 w).

  Definition Q_stack_frame (u: V) (s0: @SCCSt V) (_: unit) (s: @SCCSt V): Prop :=
    forall anc,
      In anc (stack s0) ->
      dfn s0 anc < dfn s0 u ->
      In anc (stack s).

  Definition Q_low_valid (u: V) (s0: @SCCSt V) (_: unit) (s: @SCCSt V): Prop :=
    low_valid_post g root u s /\
    u ∈ visited s /\
    stack_dfn_order s /\
    dfn_injective s.

  Theorem tarjan_scc_keep_fa_stable (u: V) (s0: @SCCSt V):
    Hoare (fun s => s = s0)
          (tarjan_scc g u)
          (Q_fa_stable u s0).
  Admitted.

  Theorem tarjan_scc_keep_stack_frame (u: V) (s0: @SCCSt V):
    Hoare (fun s => s = s0 /\ stack_dfn_order s /\ dfn_injective s)
          (tarjan_scc g u)
          (Q_stack_frame u s0).
  Admitted.

  (* Compatibility name kept for older local scripts. *)
  Theorem tarjan_scc_keep_fa (u: V) (s_init: @SCCSt V):
    Hoare (fun s => s = s_init)
          (tarjan_scc g u)
          (fun _ s => forall w,
             w ∈ visited s_init -> fa s w = fa s_init w).
  Admitted.

  (* ================================================================ *)
  (* Forset phase contracts                                          *)
  (* ================================================================ *)

  Definition low_continuation_contract
             (W: V -> program (@SCCSt V) unit)
             (u a: V) (done: V -> Prop) (s0: @SCCSt V): Prop :=
    ~ a ∈ visited s0 ->
    low_iteration_inv g root u done s0 ->
    stack_dfn_order s0 ->
    dfn_injective s0 ->
    Hoare (fun s => s = s0)
          (W a)
          (fun _ s =>
             Q_low_valid a s0 tt s /\
             Q_fa_stable a s0 tt s /\
             Q_stack_frame a s0 tt s /\
             low_iteration_inv g root u done s /\
             (fa s0 a = u -> fa s a = u)).

  Lemma process_edge_preserves_low_iteration
        (u a: V) (done: V -> Prop) (s0: @SCCSt V)
        (W: V -> program (@SCCSt V) unit):
    low_continuation_contract W u a done s0 ->
    dg_step g u a ->
    ~ done a ->
    Hoare (fun s => s = s0 /\ low_iteration_inv g root u done s /\
                     stack_dfn_order s /\ dfn_injective s /\
                     dg_step g u a /\ ~ done a)
          (process_edge u W a)
          (fun _ s => low_iteration_inv g root u (done ∪ [a]) s /\
                      stack_dfn_order s /\ dfn_injective s).
  Admitted.

  Lemma forset_preserves_low_iteration
        (u: V) (W: V -> program (@SCCSt V) unit):
    (forall a done s0,
       dg_step g u a ->
       ~ done a ->
       low_continuation_contract W u a done s0) ->
    Hoare (fun s => low_iteration_entry g root u s)
          (forset (fun v => dg_step g u v) (process_edge u W))
          (fun _ s => low_iteration_done g root u s).
  Admitted.

  (* ================================================================ *)
  (* Top-level low-link theorems                                     *)
  (* ================================================================ *)

  Theorem tarjan_scc_keep_low_valid (u: V):
    Hoare (fun s => low_pre g root u s /\ stack_dfn_order s /\ dfn_injective s)
          (tarjan_scc g u)
          (fun _ s => low_valid_post g root u s /\
                      u ∈ visited s /\
                      stack_dfn_order s /\
                      dfn_injective s).
  Admitted.

  Theorem tarjan_scc_keep_is_low (u: V):
    Hoare (fun s => low_pre g root u s /\ stack_dfn_order s /\ dfn_injective s)
          (tarjan_scc g u)
          (fun _ s => low_post g root u s /\
                      u ∈ visited s /\
                      stack_dfn_order s /\
                      dfn_injective s).
  Admitted.

End IS_LOW.
