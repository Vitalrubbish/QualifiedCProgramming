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
From SimpleC.EE.QCP_demos_human Require Import eval_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.

From SimpleC.EE.QCP_demos_human Require Import eval_lib.
Local Open Scope sac.

(* Locally use Z.eqb_eq *)
Local Hint Resolve Z.eqb_eq : core.

Lemma proof_of_eval_return_wit_28 : eval_return_wit_28.
Proof.
  pre_process.
  subst.
  entailer!.
Qed.

Lemma proof_of_eval_return_wit_27 : eval_return_wit_27.
Proof.
  pre_process.
  subst.
  entailer!.
Qed.

Lemma proof_of_eval_return_wit_26 : eval_return_wit_26.
Proof.
  pre_process.
  subst. simpl. rewrite <- PreH5.
  Exists v_2 v.
  entailer!.
  destruct op; try discriminate; auto.
  destruct (expr_eval e1 l =? 0)%Z eqn : I; try lia.
  destruct (expr_eval e2 l =? 0)%Z eqn : J; try lia.
Qed.

Lemma proof_of_eval_return_wit_25 : eval_return_wit_25.
Proof.
  pre_process.
  subst. simpl. rewrite <- PreH5.
  Exists v_2 v.
  entailer!.
  destruct op; try discriminate; auto.
  destruct (expr_eval e1 l =? 0)%Z eqn : I; try lia.
  destruct (expr_eval e2 l =? 0)%Z eqn : J; try lia.
Qed.

Lemma proof_of_eval_return_wit_24 : eval_return_wit_24.
Proof.
  pre_process.
  subst.
  simpl. rewrite <- PreH4.
  Exists v_2 v.
  entailer!.
  destruct op ; try discriminate ; auto.
  destruct (expr_eval e1 l =? 0)%Z eqn : I; try lia.
Qed.

Lemma proof_of_eval_return_wit_23 : eval_return_wit_23.
Proof.
  pre_process.
  subst.
  simpl. rewrite <- PreH5.
  Exists v_2 v.
  entailer!.
  destruct op ; try discriminate ; auto.
  destruct (expr_eval e1 l =? 0)%Z eqn : I; try lia.
Qed. 

Lemma proof_of_eval_return_wit_22 : eval_return_wit_22.
Proof.
  pre_process.
  subst.
  simpl. rewrite <- PreH6.
  Exists v_2 v.
  entailer!.
  destruct op ; try discriminate ; auto.
  destruct (expr_eval e1 l =? 0)%Z eqn : I; try lia.
  destruct (expr_eval e2 l =? 0)%Z eqn : J; try lia.
Qed.

Lemma proof_of_eval_return_wit_21 : eval_return_wit_21.
Proof.
  pre_process.
  subst.
  simpl. rewrite <- PreH6. 
  Exists v_2 v.
  entailer!.
  destruct op ; try discriminate ; auto.
  destruct (expr_eval e1 l =? 0)%Z eqn : I; try lia.
  destruct (expr_eval e2 l =? 0)%Z eqn : J; try lia.
Qed. 

Lemma proof_of_eval_return_wit_20 : eval_return_wit_20.
Proof.
  pre_process.
  subst. simpl. rewrite PreH11.
  Exists v_2 v.
  entailer!.
  destruct op; try discriminate; auto.
Qed.

Lemma proof_of_eval_return_wit_19 : eval_return_wit_19.
Proof. 
  pre_process.
  subst. simpl. rewrite PreH12.
  Exists v_2 v.
  entailer!.
  destruct op; try discriminate; auto.
Qed.

Lemma proof_of_eval_return_wit_18 : eval_return_wit_18.
Proof. 
  pre_process.
  subst. simpl. rewrite PreH13.
  Exists v_2 v.
  entailer!.
  destruct op; try discriminate; auto.
Qed.

Lemma proof_of_eval_return_wit_17 : eval_return_wit_17.
Proof.
  pre_process.
  subst. simpl. rewrite <- PreH14.
  Exists v_2 v.
  entailer!.
  destruct op; try discriminate; auto.
Qed.

Lemma proof_of_eval_return_wit_16 : eval_return_wit_16.
Proof.
  pre_process.
  subst. simpl. rewrite <- PreH15.
  Exists v_2 v.
  entailer!.
  destruct op; try discriminate; auto.
Qed.

Lemma proof_of_eval_return_wit_15 : eval_return_wit_15.
Proof.
  pre_process.
  subst.
  simpl. rewrite <- PreH17. 
  Exists v_2 v.
  entailer!.
  destruct op; try discriminate; auto.
  destruct (expr_eval e1 l <? expr_eval e2 l)%Z eqn : I; lia.
Qed.

Lemma proof_of_eval_return_wit_14 : eval_return_wit_14.
Proof.
  pre_process.
  subst.
  simpl. rewrite <- PreH17.
  Exists v_2 v.
  entailer!.
  destruct op; try discriminate; auto.
  destruct (expr_eval e1 l <? expr_eval e2 l)%Z eqn : I; lia.
Qed.

Lemma proof_of_eval_return_wit_13 : eval_return_wit_13.
Proof.
  pre_process.
  subst.
  simpl. rewrite <- PreH18.
  Exists v_2 v.
  entailer!.
  destruct op; try discriminate; auto.
  destruct (expr_eval e1 l >? expr_eval e2 l)%Z eqn : I; lia.
Qed.

Lemma proof_of_eval_return_wit_12 : eval_return_wit_12.
Proof.
  pre_process.
  subst.
  simpl. rewrite <- PreH18.
  Exists v_2 v.
  entailer!.
  destruct op; try discriminate; auto.
  destruct (expr_eval e1 l >? expr_eval e2 l)%Z eqn : I; lia.
Qed.

Lemma proof_of_eval_return_wit_11 : eval_return_wit_11.
Proof.
  pre_process.
  subst. simpl. rewrite <- PreH19.
  Exists v_2 v.
  entailer!.
  destruct op; try discriminate; auto.
  destruct (expr_eval e1 l <=? expr_eval e2 l)%Z eqn : I; lia.
Qed.

Lemma proof_of_eval_return_wit_10 : eval_return_wit_10.
Proof.
  pre_process.
  subst. simpl. rewrite <- PreH19.
  Exists v_2 v.
  entailer!.
  destruct op; try discriminate; auto.
  destruct (expr_eval e1 l <=? expr_eval e2 l)%Z eqn : I; lia.
Qed.

Lemma proof_of_eval_return_wit_9 : eval_return_wit_9.
Proof.
  pre_process.
  subst. simpl. rewrite <- PreH20.
  Exists v_2 v.
  entailer!.
  destruct op; try discriminate; auto.
  destruct (expr_eval e1 l >=? expr_eval e2 l)%Z eqn : I; lia.
Qed.

Lemma proof_of_eval_return_wit_8 : eval_return_wit_8.
Proof.
  pre_process.
  subst. simpl. rewrite <- PreH20.
  Exists v_2 v.
  entailer!.
  destruct op; try discriminate; auto.
  destruct (expr_eval e1 l >=? expr_eval e2 l)%Z eqn : I; lia.
Qed. 

Lemma proof_of_eval_return_wit_7 : eval_return_wit_7.
Proof.
  pre_process.
  subst. simpl. rewrite <- PreH21.
  Exists v_2 v.
  entailer!.
  destruct op; try discriminate; auto.
  destruct (expr_eval e1 l =? expr_eval e2 l)%Z eqn : I; lia.
Qed.

Lemma proof_of_eval_return_wit_6 : eval_return_wit_6.
Proof.
  pre_process.
  subst. simpl. rewrite <- PreH21.
  Exists v_2 v.
  entailer!.
  destruct op; try discriminate; auto.
  destruct (expr_eval e1 l =? expr_eval e2 l)%Z eqn : I; try lia.
Qed.

Lemma proof_of_eval_return_wit_5 : eval_return_wit_5.
Proof.
  pre_process.
  subst. simpl. rewrite <- PreH22.
  Exists v_2 v.
  entailer!.
  destruct op; try discriminate; auto. simpl.
  destruct (expr_eval e1 l =? expr_eval e2 l)%Z eqn : I; try lia.
Qed.

Lemma proof_of_eval_return_wit_4 : eval_return_wit_4.
Proof.
  pre_process.
  subst. simpl. rewrite <- PreH22. 
  Exists v_2 v.
  entailer!.
  destruct op; try discriminate; auto.
  destruct (expr_eval e1 l =? expr_eval e2 l)%Z eqn : I; try lia.
Qed.

Lemma proof_of_eval_return_wit_3 : eval_return_wit_3.
Proof.
  pre_process.
  subst. simpl.
  rewrite <- PreH5.
  get_un_op_from_id op.
  Exists v.
  entailer!.
  destruct ((expr_eval e1 l =? 0)%Z) eqn: I; lia.
Qed.

Lemma proof_of_eval_return_wit_2 : eval_return_wit_2.
Proof.
  pre_process.
  subst.
  rewrite PreH5.
  get_un_op_from_id op.
  simpl store_expr.
  Exists v.
  entailer!.
  simpl.
  destruct ((expr_eval e1 l =? 0)%Z) eqn: I; lia.
Qed. 

Lemma proof_of_eval_return_wit_1 : eval_return_wit_1.
Proof.
  pre_process.
  subst.
  destruct op.
  1: { simpl in PreH2. contradiction. } 
  simpl store_expr.
  Exists v.
  entailer!.
Qed.

Lemma proof_of_eval_partial_solve_wit_6_pure : eval_partial_solve_wit_6_pure.
Proof.
  pre_process.
  subst.
  rewrite PreH4.
  get_bin_op_from_id op.
  inversion PreH5; subst.
  entailer!.
Qed.

Lemma proof_of_eval_partial_solve_wit_7_pure : eval_partial_solve_wit_7_pure.
Proof.
  pre_process.
  subst.
  rewrite PreH4.
  get_bin_op_from_id op.
  inversion PreH5; subst.
  entailer!.
Qed. 

Lemma proof_of_eval_partial_solve_wit_8_pure : eval_partial_solve_wit_8_pure.
Proof.
  pre_process.
  subst.
  rewrite PreH5.
  get_bin_op_from_id op.
  inversion PreH6; subst.
  entailer!.
Qed.

Lemma proof_of_eval_partial_solve_wit_9_pure : eval_partial_solve_wit_9_pure.
Proof.
  pre_process.
  subst.
  rewrite PreH5.
  get_bin_op_from_id op.
  inversion PreH6; subst.
  entailer!.
Qed.

Lemma proof_of_eval_partial_solve_wit_10_pure : eval_partial_solve_wit_10_pure.
Proof.
  pre_process.
  subst.
  inversion PreH6.
  entailer!.
Qed.

Lemma proof_of_eval_partial_solve_wit_11_pure : eval_partial_solve_wit_11_pure.
Proof.
  pre_process.
  subst.
  inversion PreH6.
  entailer!.
Qed.

Lemma proof_of_eval_partial_solve_wit_13_pure : eval_partial_solve_wit_13_pure.
Proof.
  pre_process.
  subst.
  inversion PreH5.
  entailer!.
Qed.

Lemma proof_of_eval_partial_solve_wit_14_pure : eval_partial_solve_wit_14_pure.
Proof.
  pre_process.
  subst.
  inversion PreH5.
  entailer!.
Qed.

Lemma proof_of_eval_which_implies_wit_1 : eval_which_implies_wit_1.
Proof.
  pre_process.
  destruct e0.
  + Exists 0.
    unfold store_expr, store_expr_aux.
    entailer!.
  + Exists 1.
    unfold store_expr, store_expr_aux.
    entailer!.
  + Exists 3.
    simpl.
    Intros p.
    Exists p.
    entailer!.
  + Exists 2.
    simpl.
    Intros p1 p2.
    Exists p1 p2.
    entailer!.
Qed.

Lemma proof_of_eval_which_implies_wit_2 : eval_which_implies_wit_2.
Proof.
  pre_process.
  subst e_t.
  unfold store_expr_aux.
  destruct e0.
  4: { Intros p1 p2. discriminate. }
  3: { Intros p1. discriminate. }
  2: { Intros. discriminate. }
  Exists z.
  entailer!.
Qed.

Lemma proof_of_eval_which_implies_wit_3 : eval_which_implies_wit_3.
Proof.
  pre_process.
  prop_apply IntArray.full_length.
  subst e_t.
  unfold store_expr_aux.
  destruct e0.
  4: { Intros p1 p2. discriminate. }
  3: { Intros p1. discriminate. }
  1: { Intros. discriminate. }
  Exists z.
  inversion PreH2.
  entailer!.
Qed.

Lemma proof_of_eval_which_implies_wit_4 : eval_which_implies_wit_4.
Proof. 
  pre_process.
  subst e_t.
  unfold store_expr_aux.
  destruct e0.
  { Intros. discriminate. }
  { Intros. discriminate. }
  { Intros p. discriminate. }
  Intros p1 p2.
  Exists p2 p1 (BinOpID b) b.
  Exists e0_1 e0_2.
  entailer!.
Qed.

Lemma proof_of_eval_which_implies_wit_5 : eval_which_implies_wit_5.
Proof.
  pre_process.
  subst e_t.
  unfold store_expr_aux.
  destruct e0.
  { Intros. discriminate. }
  { Intros. discriminate. }
  2: { Intros p1 p2. discriminate. }
  Intros p.
  Exists p (UnOpID u) u.
  Exists e0.
  entailer!.
Qed. 

Lemma proof_of_eval_safety_wit_13 : eval_safety_wit_13.
Proof.
  pre_process.
  subst.
  destruct op ; try discriminate ; auto.
  inversion PreH7. entailer! ; simpl in * ; try lia.
Qed.

Lemma proof_of_eval_safety_wit_15 : eval_safety_wit_15.
Proof.
  pre_process.
  subst.
  destruct op ; try discriminate ; auto.
  inversion PreH7. entailer! ; simpl in * ; try lia.
Qed.

Lemma proof_of_eval_safety_wit_17 : eval_safety_wit_17.
Proof.
  pre_process.
  subst.
  destruct op ; try discriminate ; auto.
  inversion PreH7. entailer! ; simpl in * ; try lia.
Qed.

Lemma proof_of_eval_safety_wit_19 : eval_safety_wit_19.
Proof.
  pre_process.
  subst.
  destruct op ; try discriminate ; auto.
  inversion PreH7. entailer! ; simpl in * ; try lia.
Qed.

Lemma proof_of_eval_safety_wit_21 : eval_safety_wit_21.
Proof.
  pre_process.
  subst.
  destruct op ; try discriminate ; auto.
  inversion PreH7. entailer! ; simpl in * ; try lia.
Qed.

Lemma proof_of_eval_safety_wit_28 : eval_safety_wit_28.
Proof.
  pre_process.
  destruct op ; simpl in PreH6 ; try discriminate ; lia.
Qed.

Lemma proof_of_eval_safety_wit_31 : eval_safety_wit_31.
Proof.
  pre_process.
  destruct op ; simpl in * ; try discriminate ; try lia.
  subst.
  inversion PreH5. subst. simpl in *.
  entailer!.
Qed.

Lemma proof_of_eval_safety_wit_32 : eval_safety_wit_32.
Proof.
  pre_process.
  destruct e0 ; simpl in * ; Intro_any ; try lia.
  Intro_any. lia.
Qed.

