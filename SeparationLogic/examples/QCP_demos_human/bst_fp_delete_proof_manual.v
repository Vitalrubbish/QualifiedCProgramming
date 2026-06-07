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
From SimpleC.EE.QCP_demos_human Require Import bst_fp_delete_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
From SimpleC.EE.QCP_demos_human Require Import bst_fp_lib.
Local Open Scope sac.

Lemma proof_of_replace_min_entail_wit_1 : replace_min_entail_wit_1.
Proof.
  pre_process.
  Exists b_pre_v nil tr.
  entailer!.
  simpl store_ptb.
  entailer!.
Qed. 

Lemma proof_of_replace_min_entail_wit_2 : replace_min_entail_wit_2.
Proof.
  pre_process.
  sep_apply (store_ptb_LH b b_v_2); [ | try tauto .. ].
  sep_apply store_ptb_app.
  sep_apply (store_tree_not_zero b_v_left b_v_2 l0); [ | try tauto .. ].
  Intros l1 k0 v0 r1 pl.
  Intros pr.
  sep_apply (store_tree_make_tree b_v_left k0 v0 pl pr b_v_2 l1 r1); [ | try tauto | try tauto].
  rewrite <-H2.
  Exists
    b_v_left
    (LH b_v_key b_v_value r0 :: pt0_2)
    l0.
  subst.
  entailer!.
Qed.

Lemma proof_of_replace_min_return_wit_1 : replace_min_return_wit_1.
Proof.
  pre_process.
  sep_apply store_tree_make_tree; [ | try tauto | try tauto].
  sep_apply store_ptb_store_tree.
  Intros p_root.
  Exists p_root b_v_value b_v_key.
  sep_apply (store_tree_zero b_v_left b_v l0); [ | try tauto].
  entailer!.
  + rewrite PreH13; rewrite PreH8; rewrite H2; simpl; rewrite PreH3; entailer!.
  + rewrite PreH11; rewrite PreH8; rewrite H2; simpl; reflexivity.
  + rewrite PreH10; rewrite PreH8; rewrite H2; simpl; reflexivity.
Qed.

Lemma proof_of_replace_min_return_wit_2 : replace_min_return_wit_2.
Proof.
  pre_process.
  sep_apply (store_tree_zero b_v_right b_v r0); [ | try tauto].
  entailer!.
  sep_apply (store_tree_zero b_v_left b_v l0); [ | try tauto].
  Intros.
  subst b_v_right.
  assert (b # Ptr |-> 0 |-- b # Ptr |-> 0 ** store_tree 0 fa empty); simpl; entailer!.
  sep_apply H3.
  sep_apply store_ptb_store_tree.
  Intros p_root.
  Exists p_root b_v_value b_v_key.
  subst.
  rewrite PreH10.
  rewrite PreH7.
  rewrite PreH8.
  simpl.
  entailer!.
Qed.

Lemma proof_of_replace_min_which_implies_wit_1 : replace_min_which_implies_wit_1.
Proof.
  pre_process.
  sep_apply store_tree_not_zero; [ | try tauto .. ].
  Intros l0 k v r0 pl.
  Intros pr.
  Exists pr pl l0 v r0.
  Exists k.
  entailer!.
Qed.

Lemma proof_of_replace_min_which_implies_wit_2 : replace_min_which_implies_wit_2.
Proof.
  pre_process.
  entailer!.
  sep_apply store_tree_not_zero; [ | try tauto .. ].
  Intros l0 k v r0 pl.
  Intros pr.
  Exists pr pl l0 v r0.
  Exists k.
  entailer!.
Qed.

Lemma proof_of_Delete_entail_wit_1 : Delete_entail_wit_1.
Proof.
  pre_process.
  Exists b_pre_v nil tr_low_level_spec.
  unfold store_ptb.
  entailer!.
Qed.

Lemma proof_of_Delete_entail_wit_2_1 : Delete_entail_wit_2_1.
Proof.
  pre_process.
  Exists
    b_v_left
    (LH b_v_key b_v_value r0 :: pt0_2)
    l0.
  sep_apply (store_ptb_LH b b_v_2); [ | try tauto .. ].
  sep_apply store_ptb_app.
  entailer!.
  rewrite <- PreH6.
  rewrite PreH4.
  simpl.
  f_equal.
  destruct (Key.dec x_pre b_v_key) as [[? | ?] | ?];
    first [reflexivity | Key.order].
Qed.

Lemma proof_of_Delete_entail_wit_2_2 : Delete_entail_wit_2_2.
Proof.
  pre_process.
  Exists
    b_v_right
    (RH b_v_key b_v_value l0 :: pt0_2)
    r0.
  sep_apply (store_ptb_RH b b_v_2); [ | try tauto .. ].
  sep_apply store_ptb_app.
  entailer!.
  rewrite <- PreH7.
  rewrite PreH5.
  simpl.
  f_equal.
  destruct (Key.dec x_pre b_v_key) as [[? | ?] | ?];
    first [reflexivity | Key.order].
Qed.

Lemma proof_of_Delete_return_wit_4 : Delete_return_wit_4.
Proof.
  pre_process.
  sep_apply store_tree_make_tree; [ | try tauto | try tauto].
  sep_apply (store_tree_zero b_v_right b_v r0); [ | try tauto].
  sep_apply store_ptb_store_tree.
  Intros p_root.
  Exists p_root.
  entailer!.
  rewrite <- PreH12.
  rewrite PreH10.
  rewrite PreH3.
  simpl.
  destruct (Key.dec x_pre b_v_key) as [[? | ?] | ?]; try Key.order.
  subst; simpl.
  entailer!.
Qed.

Lemma proof_of_Delete_return_wit_5 : Delete_return_wit_5.
Proof.
  pre_process.
  sep_apply (store_tree_zero b_v_right b_v r0); [ | try tauto].
  entailer!.
  rewrite PreH1.
  sep_apply store_tree_zero; [ | try tauto].
  entailer!.
  assert (b # Ptr |-> 0 |-- b # Ptr |-> 0 ** store_tree 0 fa empty); simpl; entailer!.
  sep_apply H3.
  sep_apply store_ptb_store_tree.
  Intros p_root.
  Exists p_root.
  rewrite <- PreH9.
  rewrite PreH7.
  rewrite H0.
  simpl.
  destruct (Key.dec x_pre b_v_key) as [[? | ?] | ?]; try Key.order.
  rewrite H2.
  reflexivity.
Qed.

Lemma proof_of_Delete_return_wit_3 : Delete_return_wit_3.
Proof.
  pre_process.
  sep_apply store_tree_make_tree; [ | try tauto | try tauto].
  sep_apply (store_tree_zero b_v_left b_v l0); [ | try tauto].
  sep_apply store_ptb_store_tree.
  Intros p_root.
  Exists p_root.
  entailer!.
  rewrite <- PreH13.
  rewrite PreH11.
  rewrite PreH3.
  simpl.
  destruct (Key.dec x_pre b_v_key) as [[? | ?] | ?]; try Key.order.
  subst; simpl.
  entailer!.
Qed.

Lemma proof_of_Delete_return_wit_2 : Delete_return_wit_2.
Proof.
  pre_process.
  sep_apply (store_tree_not_zero b_v_left b_v l0); [ | try tauto].
  Intros l1 k v r1 pl.
  Intros pr.
  sep_apply (store_tree_make_tree b_v_left); [ | try tauto | try tauto].
  sep_apply store_tree_make_tree; [ | try tauto | try tauto].
  sep_apply store_ptb_store_tree.
  Intros p_root.
  Exists p_root.
  rewrite <- PreH16.
  rewrite PreH14.
  rewrite PreH7.
  rewrite H0.
  unfold tree_delete.
  destruct (Key.dec x_pre b_v_key) as [[? | ?] | ?]; try Key.order.
  rewrite <- PreH2.
  rewrite <- PreH1.
  entailer!.
Qed.

Lemma proof_of_Delete_return_wit_1 : Delete_return_wit_1.
Proof.
  pre_process.
  sep_apply store_tree_zero; [ | try tauto].
  entailer!.
  assert (b # Ptr |-> b_v |-- b # Ptr |-> b_v ** store_tree b_v fa tr0).
  subst.
  simpl.
  entailer!.
  sep_apply H1.
  sep_apply store_ptb_store_tree.
  Intros p_root.
  Exists p_root.
  rewrite <- PreH2.
  rewrite H0.
  simpl.
  entailer!.
Qed.

Lemma proof_of_Delete_which_implies_wit_1 : Delete_which_implies_wit_1.
Proof.
  pre_process.
  sep_apply store_tree_not_zero; [ | try tauto].
  Intros l0 k v r0 pl.
  Intros pr.
  Exists pr pl l0 v r0.
  Exists k.
  entailer!.
Qed.

Lemma proof_of_Delete_which_implies_wit_2 : Delete_which_implies_wit_2.
Proof.
  pre_process.
  sep_apply store_tree_not_zero; [ | try tauto].
  Intros l0 k v r0 pl.
  Intros pr.
  Exists pr pl l0 v r0.
  Exists k.
  entailer!.
Qed.

Lemma proof_of_Delete_which_implies_wit_3 : Delete_which_implies_wit_3.
Proof.
  pre_process.
  sep_apply store_tree_not_zero; [ | try tauto].
  Intros l0 k v r0 pl.
  Intros pr.
  Exists pr pl l0 v r0.
  Exists k.
  entailer!.
Qed.

Lemma proof_of_Delete_which_implies_wit_4 : Delete_which_implies_wit_4.
Proof.
  pre_process.
  sep_apply store_tree_not_zero; [ | try tauto].
  Intros l0 k v r0 pl.
  Intros pr.
  Exists pr pl l0 v r0.
  Exists k.
  entailer!.
Qed.

Lemma proof_of_Delete_derive_high_level_spec_by_low_level_spec : Delete_derive_high_level_spec_by_low_level_spec.
Proof.
  pre_process.
  Intros b_pre_v.
  unfold Bst.store_map.
  Intros tr.
  Exists tr.
  Exists b_pre_v.
  entailer!.
  apply derivable1_wand_sepcon_adjoint.
  Intros b_post_v.
  Exists b_post_v.
  Exists (tree_delete x_pre tr).
  entailer!.
  + apply delete_Abs; tauto.
  + apply delete_SearchTree; tauto.
Qed.
