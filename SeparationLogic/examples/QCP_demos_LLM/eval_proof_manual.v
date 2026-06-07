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
From SimpleC.EE.QCP_demos_LLM Require Import eval_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.QCP_demos_LLM.eval_lib.
Local Open Scope sac.

Lemma proof_of_eval_safety_wit_13 : eval_safety_wit_13.
Proof.
  pre_process.
  rewrite PreH8 in PreH9.
  assert (Hop: op = T_plus)
    by (destruct op; simpl in PreH9; try discriminate; reflexivity).
  rewrite PreH7 in PreH5.
  rewrite Hop in PreH5.
  inversion PreH5 as [| | | ? ? ? ? _ _ Hbc]; subst.
  unfold bin_safe_cond in Hbc; simpl in Hbc.
  entailer!.
Qed.

Lemma proof_of_eval_safety_wit_15 : eval_safety_wit_15.
Proof.
  pre_process.
  rewrite PreH8 in PreH10.
  assert (Hop: op = T_minus)
    by (destruct op; simpl in PreH10; try discriminate; reflexivity).
  rewrite PreH7 in PreH5.
  rewrite Hop in PreH5.
  inversion PreH5 as [| | | ? ? ? ? _ _ Hbc]; subst.
  unfold bin_safe_cond in Hbc; simpl in Hbc.
  entailer!.
Qed.

Lemma proof_of_eval_safety_wit_17 : eval_safety_wit_17.
Proof.
  pre_process.
  rewrite PreH8 in PreH11.
  assert (Hop: op = T_mul)
    by (destruct op; simpl in PreH11; try discriminate; reflexivity).
  rewrite PreH7 in PreH5.
  rewrite Hop in PreH5.
  inversion PreH5 as [| | | ? ? ? ? _ _ Hbc]; subst.
  unfold bin_safe_cond in Hbc; simpl in Hbc.
  entailer!.
Qed.

Lemma proof_of_eval_safety_wit_19 : eval_safety_wit_19.
Proof.
  pre_process.
  rewrite PreH8 in PreH12.
  assert (Hop: op = T_div)
    by (destruct op; simpl in PreH12; try discriminate; reflexivity).
  rewrite PreH7 in PreH5.
  rewrite Hop in PreH5.
  inversion PreH5 as [| | | ? ? ? ? _ _ Hbc]; subst.
  unfold bin_safe_cond in Hbc; simpl in Hbc.
  entailer!.
Qed.

Lemma proof_of_eval_safety_wit_21 : eval_safety_wit_21.
Proof.
  pre_process.
  rewrite PreH8 in PreH13.
  assert (Hop: op = T_mod)
    by (destruct op; simpl in PreH13; try discriminate; reflexivity).
  rewrite PreH7 in PreH5.
  rewrite Hop in PreH5.
  inversion PreH5 as [| | | ? ? ? ? _ _ Hbc]; subst.
  unfold bin_safe_cond in Hbc; simpl in Hbc.
  entailer!.
Qed.

Lemma proof_of_eval_safety_wit_28 : eval_safety_wit_28.
Proof.
  pre_process.
  destruct op; simpl in PreH8; subst v; lia.
Qed.

Lemma proof_of_eval_safety_wit_31 : eval_safety_wit_31.
Proof.
  pre_process.
  assert (Hop: op = T_uminus).
  { destruct op; simpl in PreH6; subst v; try reflexivity; lia. }
  subst op.
  rewrite PreH5 in PreH3.
  apply safe_eval_un_cond in PreH3.
  unfold un_safe_cond in PreH3.
  entailer!.
Qed.

Lemma proof_of_eval_safety_wit_32 : eval_safety_wit_32.
Proof.
  pre_process.
  destruct e0; simpl in *; Intro_any; try lia.
  Intro_any. lia.
Qed.

Lemma proof_of_eval_entail_wit_1 : eval_entail_wit_1.
Proof.
  pre_process; destruct e0; simpl.
  - Exists 0. pre_process.
  - Exists 1. pre_process.
  - Intros p. Exists 3 p. pre_process.
  - Intros p1 p2. Exists 2 p1 p2. pre_process.
Qed.

Lemma proof_of_eval_entail_wit_2 : eval_entail_wit_2.
Proof.
  pre_process; destruct e0; simpl.
  - Exists z e_t_2. pre_process.
  - pre_process; lia.
  - Intros p'. pre_process; lia.
  - Intros p1 p2. pre_process; lia.
Qed.

Lemma proof_of_eval_entail_wit_3 : eval_entail_wit_3.
Proof.
  pre_process.
  prop_apply IntArray.full_Zlength.
  Intros_p Hlen.
  destruct e0; simpl.
  - pre_process; lia.
  - Exists e_t_2 z.
    inversion PreH1; subst.
    pre_process.
    split_pure_spatial.
    + pre_process.
    + split_pures.
      * dump_pre_spatial. assumption.
      * dump_pre_spatial. lia.
      * dump_pre_spatial. rewrite Zlength_correct in Hlen; lia.
      * dump_pre_spatial. reflexivity.
      * dump_pre_spatial. reflexivity.
  - Intros p'. pre_process; lia.
  - Intros p1 p2. pre_process; lia.
Qed.

Lemma proof_of_eval_entail_wit_4 : eval_entail_wit_4.
Proof.
  pre_process.
  subst e_t_2.
  destruct e0; simpl.
  - pre_process; lia.
  - pre_process; lia.
  - Intros p'. pre_process; lia.
  - Intros p1 p2.
    Exists p2 p1.
    Exists (BinOpID b) b e0_1 e0_2 2.
    pre_process.
Qed.

Lemma proof_of_eval_entail_wit_5 : eval_entail_wit_5.
Proof.
  pre_process.
  subst e_t_2.
  destruct e0; simpl.
  - pre_process; lia.
  - pre_process; lia.
  - Intros p'.
    Exists p' (UnOpID u) u e0 3.
    pre_process.
  - Intros p1 p2. pre_process; lia.
Qed.

Ltac solve_eval_pure :=
  simpl in *;
  repeat match goal with
  | H: ?x = expr_eval ?e ?l |- context[expr_eval ?e ?l] => rewrite <- H
  | H: expr_eval ?e ?l = ?x |- context[expr_eval ?e ?l] => rewrite H
  end;
  simpl in *;
  repeat match goal with
  | H: ?x <> ?y |- context[Z.eqb ?x ?y] =>
      let Hcmp := fresh "Hcmp" in
      destruct (Z.eqb x y) eqn:Hcmp; [apply Z.eqb_eq in Hcmp; lia|simpl]
  | H: ?x <> ?y |- context[Z.eqb ?y ?x] =>
      let Hcmp := fresh "Hcmp" in
      destruct (Z.eqb y x) eqn:Hcmp; [apply Z.eqb_eq in Hcmp; lia|simpl]
  | |- context[Z.eqb ?x ?y] =>
      let Hcmp := fresh "Hcmp" in
      destruct (Z.eqb x y) eqn:Hcmp; [apply Z.eqb_eq in Hcmp|apply Z.eqb_neq in Hcmp]; simpl in *; try lia
  | |- context[Z.ltb ?x ?y] =>
      let Hcmp := fresh "Hcmp" in
      destruct (Z.ltb x y) eqn:Hcmp; [apply Z.ltb_lt in Hcmp|apply Z.ltb_ge in Hcmp]; simpl in *; try lia
  | |- context[Z.leb ?x ?y] =>
      let Hcmp := fresh "Hcmp" in
      destruct (Z.leb x y) eqn:Hcmp; [apply Z.leb_le in Hcmp|apply Z.leb_gt in Hcmp]; simpl in *; try lia
  | |- context[Z.geb ?x ?y] =>
      let Hcmp := fresh "Hcmp" in
      destruct (Z.geb x y) eqn:Hcmp;
      [apply Z.geb_le in Hcmp|rewrite Z.geb_leb in Hcmp; apply Z.leb_gt in Hcmp];
      simpl in *; try lia
  | |- context[Z.gtb ?x ?y] =>
      let Hcmp := fresh "Hcmp" in
      destruct (Z.gtb x y) eqn:Hcmp;
      [apply Z.gtb_lt in Hcmp|rewrite Z.gtb_ltb in Hcmp; apply Z.ltb_ge in Hcmp];
      simpl in *; try lia
  | |- context[(expr_eval ?e ?l =? 0)%Z] =>
      let Hcmp := fresh "Hcmp" in
      destruct (Z.eqb (expr_eval e l) 0) eqn:Hcmp; [apply Z.eqb_eq in Hcmp|apply Z.eqb_neq in Hcmp]; simpl in *; try lia
  end;
  repeat match goal with
  | H: 0 = ?x |- 1 = (if (?x =? 0) then 1 else 0) =>
      rewrite <- H; reflexivity
  | H: ?x = 0 |- 1 = (if (?x =? 0) then 1 else 0) =>
      rewrite H; reflexivity
  | H: ?x <> 0 |- 0 = (if (?x =? 0) then 1 else 0) =>
      let Hcmp := fresh "Hcmp" in
      destruct (Z.eqb x 0) eqn:Hcmp; [apply Z.eqb_eq in Hcmp; lia|reflexivity]
  | H: 0 <> ?x |- 0 = (if (?x =? 0) then 1 else 0) =>
      let Hcmp := fresh "Hcmp" in
      destruct (Z.eqb x 0) eqn:Hcmp; [apply Z.eqb_eq in Hcmp; lia|reflexivity]
  end;
  try dump_pre_spatial;
  try lia; try reflexivity.

Ltac solve_eval_return :=
  pre_process; subst; simpl in *;
  repeat match goal with
  | H: BinOpID ?op = ?n |- _ => destruct op; simpl in H; try discriminate; subst; simpl in *
  | H: ?n = BinOpID ?op |- _ => destruct op; simpl in H; try discriminate; subst; simpl in *
  | H: UnOpID ?op = ?n |- _ => destruct op; simpl in H; try discriminate; subst; simpl in *
  | H: ?n = UnOpID ?op |- _ => destruct op; simpl in H; try discriminate; subst; simpl in *
  | op: binop |- _ => destruct op; simpl in *; try discriminate
  | op: unop |- _ => destruct op; simpl in *; try discriminate
  end;
  repeat match goal with
  | |- context [EX _ : Z, EX _ : Z, _] =>
      match goal with
      | v_2: Z, v_3: Z |- _ => Exists v_2 v_3
      end
  | |- context [EX _ : Z, _] =>
      match goal with
      | v_2: Z |- _ => Exists v_2
      end
  end;
  first
    [ solve [pre_process]
    | pre_process; split_pure_spatial; [pre_process | dump_pre_spatial] ].

Ltac cancel_eval_binop_spatial p arr vals p1 p2 :=
  match goal with
  | H: ?e0v = EBinop ?op ?e1 ?e2 |- _ =>
      sep_apply_r_atomic (store_expr_binop_intro p op e1 e2 p1 p2)
  end;
  cancel (IntArray.full arr 100 vals);
  match goal with
  | H: ?e0v = EBinop ?op ?e1 ?e2 |- _ =>
      cancel (store_expr p2 e2);
      cancel (store_expr p1 e1)
  end;
  cancel (&( p # "expr" ->ₛ "t") # Int |-> 2);
  match goal with
  | H: ?e0v = EBinop ?op ?e1 ?e2 |- _ =>
      cancel (&( p # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op") # Int |-> BinOpID op)
  end;
  cancel (&( p # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left") # Ptr |-> p1);
  cancel (&( p # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right") # Ptr |-> p2).

Ltac solve_eval_binop_return p arr vals p1 p2 :=
  pre_process;
  match goal with
  | Hv: ?v = BinOpID ?op, Hid: ?id = ?v |- _ =>
      rewrite Hv in Hid;
      destruct op; simpl in Hid; try lia
  | Hv: ?v = BinOpID ?op, Hid: ?v = ?id |- _ =>
      rewrite Hv in Hid;
      destruct op; simpl in Hid; try lia
  end;
  match goal with
  | Ht: ?et = 2, He: ?e0v = EBinop ?op ?e1 ?e2, Hv: ?vid = BinOpID ?op |- _ =>
      rewrite Ht, He, Hv
  end;
  pre_process;
  split_pure_spatial;
  [ cancel_eval_binop_spatial p arr vals p1 p2
  | solve_eval_pure ].

Lemma proof_of_eval_return_wit_1 : eval_return_wit_1.
Proof. solve_eval_return. Qed.
Lemma proof_of_eval_return_wit_2 : eval_return_wit_2.
Proof. solve_eval_return. solve_eval_pure. Qed.
Lemma proof_of_eval_return_wit_3 : eval_return_wit_3.
Proof.
  solve_eval_return.
  destruct (Z.eqb (expr_eval e1 l) 0) eqn:Heq.
  - apply Z.eqb_eq in Heq. lia.
  - apply Z.eqb_neq in Heq. lia.
Qed.
Lemma proof_of_eval_return_wit_4 : eval_return_wit_4.
Proof. solve_eval_binop_return e_pre var_value_pre l v_2 v_3. Qed.
Lemma proof_of_eval_return_wit_5 : eval_return_wit_5.
Proof. solve_eval_binop_return e_pre var_value_pre l v_2 v_3. Qed.
Lemma proof_of_eval_return_wit_6 : eval_return_wit_6.
Proof. solve_eval_binop_return e_pre var_value_pre l v_2 v_3. Qed.
Lemma proof_of_eval_return_wit_7 : eval_return_wit_7.
Proof. solve_eval_binop_return e_pre var_value_pre l v_2 v_3. Qed.
Lemma proof_of_eval_return_wit_8 : eval_return_wit_8.
Proof. solve_eval_binop_return e_pre var_value_pre l v_2 v_3. Qed.
Lemma proof_of_eval_return_wit_9 : eval_return_wit_9.
Proof. solve_eval_binop_return e_pre var_value_pre l v_2 v_3. Qed.
Lemma proof_of_eval_return_wit_10 : eval_return_wit_10.
Proof. solve_eval_binop_return e_pre var_value_pre l v_2 v_3. Qed.
Lemma proof_of_eval_return_wit_11 : eval_return_wit_11.
Proof. solve_eval_binop_return e_pre var_value_pre l v_2 v_3. Qed.
Lemma proof_of_eval_return_wit_12 : eval_return_wit_12.
Proof. solve_eval_binop_return e_pre var_value_pre l v_2 v_3. Qed.
Lemma proof_of_eval_return_wit_13 : eval_return_wit_13.
Proof. solve_eval_binop_return e_pre var_value_pre l v_2 v_3. Qed.
Lemma proof_of_eval_return_wit_14 : eval_return_wit_14.
Proof. solve_eval_binop_return e_pre var_value_pre l v_2 v_3. Qed.
Lemma proof_of_eval_return_wit_15 : eval_return_wit_15.
Proof. solve_eval_binop_return e_pre var_value_pre l v_2 v_3. Qed.
Lemma proof_of_eval_return_wit_16 : eval_return_wit_16.
Proof. solve_eval_binop_return e_pre var_value_pre l v_2 v_3. Qed.
Lemma proof_of_eval_return_wit_17 : eval_return_wit_17.
Proof. solve_eval_binop_return e_pre var_value_pre l v_2 v_3. Qed.
Lemma proof_of_eval_return_wit_18 : eval_return_wit_18.
Proof. solve_eval_binop_return e_pre var_value_pre l v_2 v_3. Qed.
Lemma proof_of_eval_return_wit_19 : eval_return_wit_19.
Proof. solve_eval_binop_return e_pre var_value_pre l v_2 v_3. Qed.
Lemma proof_of_eval_return_wit_20 : eval_return_wit_20.
Proof. solve_eval_binop_return e_pre var_value_pre l v_2 v_3. Qed.
Lemma proof_of_eval_return_wit_21 : eval_return_wit_21.
Proof. solve_eval_binop_return e_pre var_value_pre l v_2 v_3. Qed.
Lemma proof_of_eval_return_wit_22 : eval_return_wit_22.
Proof. solve_eval_binop_return e_pre var_value_pre l v_2 v_3. Qed.
Lemma proof_of_eval_return_wit_23 : eval_return_wit_23.
Proof. solve_eval_binop_return e_pre var_value_pre l v_2 v_3. Qed.
Lemma proof_of_eval_return_wit_24 : eval_return_wit_24.
Proof. solve_eval_binop_return e_pre var_value_pre l v_2 v_3. Qed.
Lemma proof_of_eval_return_wit_25 : eval_return_wit_25.
Proof. solve_eval_binop_return e_pre var_value_pre l v_2 v_3. Qed.
Lemma proof_of_eval_return_wit_26 : eval_return_wit_26.
Proof. solve_eval_binop_return e_pre var_value_pre l v_2 v_3. Qed.
Lemma proof_of_eval_return_wit_27 : eval_return_wit_27.
Proof. solve_eval_return. Qed.
Lemma proof_of_eval_return_wit_28 : eval_return_wit_28.
Proof. solve_eval_return. Qed.

Lemma proof_of_eval_partial_solve_wit_2_pure : eval_partial_solve_wit_2_pure.
Proof. pre_process; dump_pre_spatial; subst; eauto using safe_eval_bin_left. Qed.
Lemma proof_of_eval_partial_solve_wit_3_pure : eval_partial_solve_wit_3_pure.
Proof. pre_process; dump_pre_spatial; subst; eauto using safe_eval_bin_right. Qed.
Lemma proof_of_eval_partial_solve_wit_4_pure : eval_partial_solve_wit_4_pure.
Proof. pre_process; dump_pre_spatial; subst; eauto using safe_eval_bin_left. Qed.
Lemma proof_of_eval_partial_solve_wit_5_pure : eval_partial_solve_wit_5_pure.
Proof. pre_process; dump_pre_spatial; subst; eauto using safe_eval_bin_right. Qed.
Lemma proof_of_eval_partial_solve_wit_6_pure : eval_partial_solve_wit_6_pure.
Proof. pre_process; dump_pre_spatial; subst; eauto using safe_eval_bin_left. Qed.
Lemma proof_of_eval_partial_solve_wit_7_pure : eval_partial_solve_wit_7_pure.
Proof. pre_process; dump_pre_spatial; subst; eauto using safe_eval_bin_right. Qed.
Lemma proof_of_eval_partial_solve_wit_8_pure : eval_partial_solve_wit_8_pure.
Proof. pre_process; dump_pre_spatial; subst; eauto using safe_eval_un_arg. Qed.
Lemma proof_of_eval_partial_solve_wit_9_pure : eval_partial_solve_wit_9_pure.
Proof. pre_process; dump_pre_spatial; subst; eauto using safe_eval_un_arg. Qed.
