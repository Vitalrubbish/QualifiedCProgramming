Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
From SimpleC.EE.QCP_demos_human Require Import bst_delete_rec_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
From SimpleC.EE.QCP_demos_human Require Import bst_lib.
Import get_right_most.
Import naive_C_Rules.
Local Open Scope sac.

Lemma proof_of_get_pre_return_wit_2 : get_pre_return_wit_2.
Proof.
  pre_process.
  subst; simpl.
  Exists t_left 0 nil l0 t_key.
  Exists t_value.
  sep_apply (store_tree_zero 0 r0).
  entailer!.
  + simpl.
    entailer!.
  + intros. simpl.
    rewrite H0.
    destruct tr_ret_right; tauto. 
  + tauto.
Qed.

Lemma proof_of_get_pre_return_wit_1 : get_pre_return_wit_1.
Proof.
  pre_process.
  Exists retval_left_2 0.
  Exists (pt_2 ++ (RH t_key t_value l0 :: nil)).
  Exists tr_ret_left_2 retval_key_2.
  Exists retval_value_2.
  entailer!.
  + rewrite PreH3.
    sep_apply (store_pt_RH t_right t_pre t_left t_key t_value l0); try tauto.
    sep_apply (store_pt_app retval t_right t_pre pt_2 (RH t_key t_value l0 :: nil)).
    entailer!. 
  + intros tr0.
    pose proof PreH2 tr0.
    pose proof combine_tree_pt_assoc (RH t_key t_value l0 :: nil) pt_2 (make_tree tr_ret_left_2 retval_key_2
    retval_value_2 tr0).
    rewrite <- H0.
    subst tr. 
    transitivity (make_tree l0 t_key t_value (tree_pre_merge r0 tr0)); simpl.
    - destruct r0; simpl; reflexivity.
    - f_equal. apply H.
Qed.


Lemma proof_of_get_pre_which_implies_wit_1 : get_pre_which_implies_wit_1.
Proof. 
  pre_process.
  sep_apply store_tree_not_zero; [ | tauto].
  Intros x k v r0.
  Intros pl pr.
  Exists pr pl x v.
  Exists r0 k.
  entailer!.
Qed.


Lemma proof_of_delete_return_wit_1 : delete_return_wit_1.
Proof. 
  pre_process.
  Exists b_pre_v_2.
  entailer!.
  sep_apply (store_tree_zero); [ | tauto].
  entailer!.
  rewrite H0.
  simpl. 
  entailer!.
Qed.

Lemma proof_of_delete_return_wit_2 : delete_return_wit_2.
Proof.
  pre_process.
  Exists b_pre_v_2.
  entailer!.
  subst tr_low_level_spec.
  simpl.
  destruct (Key.dec x_pre p_key) as [[? | ?] | ?]; try Key.order.
  sep_apply store_tree_make_tree; try tauto.
  entailer!.
Qed.

Lemma proof_of_delete_return_wit_3 : delete_return_wit_3.
Proof. 
  pre_process.
  Exists b_pre_v_2.
  entailer!.
  subst tr_low_level_spec.
  simpl.
  destruct (Key.dec x_pre p_key) as [[? | ?] | ?];
    try Key.order.
  sep_apply store_tree_make_tree; try tauto.
  entailer!.
Qed.

Lemma proof_of_delete_return_wit_4 : delete_return_wit_4.
Proof. 
  pre_process.
  Exists p_right.
  entailer!.
  sep_apply (store_tree_zero); [ | tauto].
  entailer!.
  subst tr_low_level_spec.
  simpl.
  destruct (Key.dec x_pre p_key) as [[? | ?] | ?]; try Key.order.
  rewrite H0.
  simpl.
  entailer!.
Qed.

Lemma proof_of_delete_return_wit_5 : delete_return_wit_5.
Proof. 
  pre_process.
  assert (x_pre = p_key) by lia.
  subst x_pre.
  Exists p_left.
  assert (Hdel: tree_delete p_key (make_tree l0 p_key p_value r0) = tree_pre_merge l0 r0).
  { simpl. destruct (Key.dec p_key p_key) as [[Hlt | Hgt] | Heq].
    - lia.
    - lia.
    - reflexivity.
  }
  rewrite PreH11, Hdel.
  assert (Hmerge: tree_pre_merge l0 r0 =
    combine_tree pt0 (make_tree tr_ret_left retval_key retval_value r0)).
  { apply PreH2. }
  rewrite Hmerge.
  cancel (b_pre # Ptr |-> p_left).
  sep_apply_l_atomic (store_tree_make_tree retval retval_key retval_value
    retval_left p_right tr_ret_left r0).
  - dump_pre_spatial. exact PreH1.
  - dump_pre_spatial. split; [exact PreH4 | exact PreH5].
  - sep_apply_l_atomic (store_combine p_left retval pt0
      (make_tree tr_ret_left retval_key retval_value r0)).
    cancel.
Qed.

Lemma proof_of_delete_which_implies_wit_1 : delete_which_implies_wit_1.
Proof. 
  pre_process.
  sep_apply store_tree_not_zero; [ | tauto].
  Intros x k v r0. 
  Intros pl pr.
  Exists pr pl x v.
  Exists r0 k.
  entailer!.
Qed.

Lemma proof_of_delete_derive_high_level_spec_by_low_level_spec : delete_derive_high_level_spec_by_low_level_spec.
Proof.
  pre_process.
  Intros b_pre_v.
  unfold Bst.store_map. Intros tr.
  Exists tr. 
  entailer!.
  Exists b_pre_v.
  entailer!.
  rewrite <- derivable1_wand_sepcon_adjoint.
  Intros b_pre_v_4.
  Exists b_pre_v_4.
  entailer!.
  Exists (tree_delete x_pre tr).
  entailer!.
  - apply delete_Abs ; auto.
  - apply delete_SearchTree ; auto. 
Qed.
