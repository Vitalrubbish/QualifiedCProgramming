Require Import Algorithms.Tarjan_directed.Tarjan_scc_is_low.

(* Re-prove W_preserves_ancestor_inv with the same signature *)
Section W_PROOF.
Context (V E: Type) (equiv0: Equivalence eq) (H0: EqDec V eq).
Context (g: OriginalGraphType V E) (OriginalGraph_gvalid0: OriginalGraph_gvalid g).
Context (root: V) (g_vvalid_root: original_vvalid g root).

Lemma W_preserves_ancestor_inv_scratch (u v: V) (done: V -> Prop):
    u <> v -> ~ done v ->
    Hoare (fun s => low_forset_inv u done s /\ fa s v = u /\ ~ v ∈ visited s /\ ~ done v /\ done_visited done s)
          (tarjan_scc (V:=V) (E:=E) (equiv0:=equiv0) (H0:=H0) g v)
          (fun _ s => low_forset_inv u done s /\ fa s v = u /\ done_visited done s).
Proof.
Admitted.

End W_PROOF.
