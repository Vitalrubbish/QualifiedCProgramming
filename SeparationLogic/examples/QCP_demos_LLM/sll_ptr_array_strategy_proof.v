Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.micromega.Psatz.
From SimpleC.SL Require Import SeparationLogic.
From SimpleC.EE.QCP_demos_LLM Require Import sll_ptr_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import SllPtrArrayLib.
Import naive_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope string.

Lemma sll_ptr_array_strategy1_correctness : sll_ptr_array_strategy1.
Proof.
  pre_process_default.
  prop_apply (SllPtrArray_full_Zlength p n rows).
  Intros.
  sep_apply_l_atomic (SllPtrArray_full_split_to_missing_i p i n rows).
  - dump_pre_spatial.
    lia.
  - Intros row_ptr.
    Exists row_ptr.
    rewrite (Znth_indep rows i nil __default_app1_Z) by lia.
    unfold StorePtrAsElement.storeA.
    entailer!.
    Intros_r v.
    apply_sepcon_adjoint.
    Intros.
    subst v.
    rewrite sizeof_ptr.
    cancel.
Qed.

Lemma sll_ptr_array_strategy4_correctness : sll_ptr_array_strategy4.
Proof.
  pre_process_default.
  Intros_p H.
  subst rows2.
  cancel.
Qed.

Lemma sll_ptr_array_strategy5_correctness : sll_ptr_array_strategy5.
Proof.
  pre_process_default.
Qed.

Lemma sll_ptr_array_strategy2_correctness : sll_ptr_array_strategy2.
Proof.
  pre_process_default.
  pose proof (SllPtrArray_missing_i_merge_to_full
        p i n row_ptr rows (Znth i rows __default_app1_Z)).
  unfold StorePtrAsElement.storeA in H1.
  rewrite sizeof_ptr.
  sep_apply H1 ; try lia.
  rewrite replace_Znth_Znth by lia.
  cancel.
Qed.
