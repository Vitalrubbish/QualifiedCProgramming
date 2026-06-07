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
From SimpleC.EE.Applications_human.cnf_trans Require Import cnf_trans_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
From SimpleC.EE.Applications_human.cnf_trans Require Import smt_lang_lib.
From SimpleC.EE.Applications_human.cnf_trans Require Import cnf_trans_lib.
From SimpleC.EE.Applications_human Require Import malloc.
From SimpleC.EE.Applications_human Require Import super_poly_sll2.
Local Open Scope sac.

Lemma proof_of_prop2cnf_safety_wit_9 : prop2cnf_safety_wit_9.
Proof.
  pre_process.
  entailer!.
  destruct prop; simpl in * ; try lia.
Qed.

Lemma proof_of_prop2cnf_entail_wit_1 : prop2cnf_entail_wit_1.
Proof.
  pre_process.
  Exists (SmtPTID prop).
  Exists z (SmtPBID op).
  Exists y 5.
  Exists clist'_2 pcnt'_2.
  Exists ccnt'_2.
  entailer!.
  subst res.
  auto.
Qed.

Lemma proof_of_prop2cnf_entail_wit_2 : prop2cnf_entail_wit_2.
Proof.
  pre_process.
  Exists p_pre_type_2.
  Exists v_5 v_4.
  Exists v_6 5.
  Exists op.
  Exists lt rt.
  Exists clist' pcnt'.
  Exists ccnt'.
  Exists clist'_3 pcnt'_3.
  Exists ccnt'_3.
  entailer!.
  subst retval.
  auto.
Qed.

Lemma proof_of_prop2cnf_entail_wit_3 : prop2cnf_entail_wit_3.
Proof.
  pre_process.
  Exists (SmtPTID prop).
  Exists (SmtPUID op) y.
  Exists t op.
  Exists sub_prop.
  Exists clist'_2 pcnt'_2.
  Exists ccnt'_2.
  entailer!.
  subst retval.
  auto.
Qed.

Lemma proof_of_prop2cnf_return_wit_3 : prop2cnf_return_wit_3.
Proof.
  pre_process.
  pose proof PreH5 as Hs1.
  pose proof PreH6 as Hs2.
  pose proof PreH7 as Hs3.
  Exists clist pcnt ccnt var.
  unfold store_predata.
  Intros y.
  Exists y.
  entailer!; rewrite PreH1 in *.
  2: {
    pose proof SmtProp_size_nonneg (SmtV var).
    lia.
  }
  2: {
    pose proof SmtProp_size_nonneg (SmtV var).
    lia.
  }
  + unfold SmtPTID, store_SmtProp.
    unfold SmtPTID.
    entailer!.
  + rewrite prop_cnt_inf_var in *.
    lia.
  + rewrite prop_cnt_inf_var in *.
    lia.
  + unfold make_predata, make_prop2cnf_ret.
    unfold prop2cnf_logic.
    reflexivity.
Qed.

Opaque Z.add Z.sub Z.mul Z.opp Z.of_nat Z.of_N Z.succ.

Lemma proof_of_prop2cnf_return_wit_2 : prop2cnf_return_wit_2.
Proof.
  pre_process.
  rewrite PreH20 in *.
  unfold SmtPTID in *.
  unfold store_predata.
  Intros y0.
  unfold iff2cnf_unary.
  repeat rewrite <- app_comm_cons.
  unfold app.
  remember (p1 :: pcnt'_2 + 1 :: 0 :: nil) as c1 eqn:H_c1.
  remember (- p1 :: - (pcnt'_2 + 1) :: 0 :: nil) as c2 eqn:H_c2.
  Exists (c1 :: c2 :: clist'_2) (pcnt'_2 + 1) (ccnt'_2 + 2) (pcnt'_2 + 1) y0.
  entailer!.
  1: {
    simpl store_SmtProp.
    subst.
    Exists v.
    entailer!.
  }
  2: {
    simpl SmtProp_size.
    repeat rewrite Zlength_cons.
    pose proof SmtProp_size_nonneg sub_prop'.
    lia.
  }
  2: {
    unfold make_prop2cnf_ret, make_predata.
    simpl.
    remember (prop2cnf_logic (sub_prop') (clist, pcnt, ccnt)) as step1 eqn:Hstep1.
    destruct step1 as [data1 p1''].  
    destruct data1 as [tmp clause_cnt].
    destruct tmp as [cnf_res prop_cnt].
    unfold make_prop2cnf_ret, make_predata in PreH13.
    rewrite <- PreH13 in Hstep1.
    inversion Hstep1.
    subst.
    reflexivity.
  }
  (* unfold make_prop2cnf_ret, make_predata in H5. *)
  unfold prop_cnt_inf.
  unfold prop_cnt_inf in PreH11.
    pose proof Z.max_lub_l _ _ _ PreH11.
    pose proof Z.max_lub_r _ _ _ PreH11.
  apply Z.max_lub; rewrite H_c1, H_c2.
  + simpl.
    assert (p1 <= pcnt'_2 + 1) by lia.
    assert (- p1 <= pcnt'_2 + 1) by lia.
    assert (0 <= pcnt'_2 + 1) by lia.
    assert (max_cnf clist'_2 <= pcnt'_2 + 1) by lia.
    repeat apply Z.max_lub; try lia.
  + simpl.
    apply Z.abs_le.
    split.
    - 
      repeat apply Z.min_glb; try lia.
    - 
      pose proof Z.le_min_l (Z.min p1 (Z.min (pcnt'_2 + 1) (Z.min 0 0)))
      (Z.min (Z.min (- p1) (Z.min (- (pcnt'_2 + 1)) (Z.min 0 0))) (min_cnf clist'_2)).
      pose proof Z.le_min_l p1 (Z.min (pcnt'_2 + 1) (Z.min 0 0)).
      remember (Z.min (Z.min p1 (Z.min (pcnt'_2 + 1) (Z.min 0 0)))
      (Z.min (Z.min (- p1) (Z.min (- (pcnt'_2 + 1)) (Z.min 0 0))) (min_cnf clist'_2))) as tmp1 eqn:H1000.
      remember (Z.min p1 (Z.min (pcnt'_2 + 1) (Z.min 0 0))) as tmp2 eqn:H2000.
      clear H1000.
      clear H2000.
      lia.
Qed.

Lemma proof_of_prop2cnf_return_wit_1 : prop2cnf_return_wit_1.
Proof.
  pre_process.
  pose proof PreH1 as Hs.
  pose proof PreH2 as Hs0.
  pose proof PreH3 as Hs1.
  pose proof PreH4 as Hs2.
  pose proof PreH7 as Hs3.
  pose proof PreH8 as Hs4.
  pose proof PreH17 as Hs5.
  pose proof PreH18 as Hs6.
  pose proof PreH25 as Hs7.
  pose proof PreH26 as Hs8.
  pose proof PreH33 as Hs9.
  pose proof PreH34 as Hs10.
  pose proof PreH35 as Hs11.
  pose proof PreH27 as Hs12.
  pose proof PreH28 as Hs13.
  pose proof PreH5 as H.
  pose proof PreH6 as H0.
  pose proof PreH9 as H1.
  pose proof PreH10 as H2.
  pose proof PreH11 as H3.
  pose proof PreH12 as H4.
  pose proof PreH13 as H5.
  pose proof PreH14 as H6.
  pose proof PreH15 as H7.
  pose proof PreH16 as H8.
  pose proof PreH19 as H11.
  pose proof PreH20 as H10.
  pose proof PreH21 as H9.
  pose proof PreH22 as H12.
  pose proof PreH23 as H13.
  pose proof PreH24 as H14.
  pose proof PreH29 as H15.
  pose proof PreH30 as H16.
  pose proof PreH31 as H17.
  pose proof PreH32 as H18.
  pose proof PreH36 as H19.
  pose proof PreH37 as H20.
  pose proof PreH38 as H21.
  pose proof PreH39 as H22.
  rewrite H15 in *.
  unfold SmtPTID in *.
  clear H19.
  unfold store_predata.
  Intros y0.
  unfold iff2cnf_binary, iff2cnf_length_binary.
  destruct op'; destruct (p1 ==? p2);
  repeat rewrite <- app_comm_cons;
  unfold app.
  + remember (p1 :: - (pcnt'_2 + 1) :: 0 :: nil) as c1 eqn:H_c1.
    remember (p2 :: - (pcnt'_2 + 1) :: 0 :: nil) as c2 eqn:H_c2.
    remember (- p1 :: pcnt'_2 + 1 :: 0 :: nil) as c3 eqn:H_c3.
    Exists (c1 :: c2 :: c3 :: clist'_2) (pcnt'_2 + 1) (ccnt'_2 + 3) (pcnt'_2 + 1) y0.
    entailer!.
    1: {
      simpl store_SmtProp.
      subst.
      Exists v_2 v.
      simpl.
      entailer!.
    }
    2: {
      repeat rewrite Zlength_cons.
      lia.
    }
    2: {
      unfold make_prop2cnf_ret, make_predata.
      simpl.
      remember (prop2cnf_logic lt' (clist, pcnt, ccnt)) as step1 eqn:Hstep1.
      destruct step1 as [data1 p1'].
      remember (prop2cnf_logic rt' data1) as step2 eqn:Hstep2.
      destruct step2 as [tmp clause_cnt].
      destruct tmp as [cnf_res prop_cnt].
      destruct cnf_res as [cnf_res0 prop_cnt0].
      unfold make_prop2cnf_ret, make_predata in H5, H9.
      rewrite <- H9 in Hstep1.
      inversion Hstep1.
      rewrite H26 in Hstep2.
      rewrite <- H5 in Hstep2.
      inversion Hstep2.
      destruct (p1 ==? p2); try contradiction.
      subst.
      reflexivity.
    }
    unfold prop_cnt_inf.
    unfold prop_cnt_inf in H3.
    pose proof Z.max_lub_l _ _ _ H3.
    pose proof Z.max_lub_r _ _ _ H3.
    apply Z.max_lub; rewrite H_c1, H_c2, H_c3.
    - simpl.
      repeat apply Z.max_lub; try lia.
    - simpl.
      apply Z.abs_le.
      split.
      * 
        repeat apply Z.min_glb; try lia.
      * 
        pose proof Z.le_min_l (Z.min p1 (Z.min (- (pcnt'_2 + 1)) (Z.min 0 0)))
        (Z.min (Z.min p2 (Z.min (- (pcnt'_2 + 1)) (Z.min 0 0)))
           (Z.min (Z.min (- p1) (Z.min (pcnt'_2 + 1) (Z.min 0 0))) (min_cnf clist'_2))).
        pose proof Z.le_min_l p1 (Z.min (- (pcnt'_2 + 1)) (Z.min 0 0)).
        remember (Z.min (Z.min p1 (Z.min (- (pcnt'_2 + 1)) (Z.min 0 0)))
        (Z.min (Z.min p2 (Z.min (- (pcnt'_2 + 1)) (Z.min 0 0)))
           (Z.min (Z.min (- p1) (Z.min (pcnt'_2 + 1) (Z.min 0 0))) (min_cnf clist'_2)))) as tmp1 eqn:H1000.
        remember (Z.min p1 (Z.min (- (pcnt'_2 + 1)) (Z.min 0 0))) as tmp2 eqn:H2000.
        clear H1000.
        clear H2000.
        lia.
  + remember (p1 :: - (pcnt'_2 + 1) :: 0 :: nil) as c1 eqn:H_c1.
    remember (p2 :: - (pcnt'_2 + 1) :: 0 :: nil) as c2 eqn:H_c2.
    remember (- p1 :: - p2 :: pcnt'_2 + 1 :: nil) as c3 eqn:H_c3.
    Exists (c1 :: c2 :: c3 :: clist'_2) (pcnt'_2 + 1) (ccnt'_2 + 3) (pcnt'_2 + 1) y0.
    entailer!.
    1: {
      simpl store_SmtProp.
      subst.
      Exists v_2 v.
      simpl.
      entailer!.
    }
    2: {
      repeat rewrite Zlength_cons.
      lia.
    }
    2: {
      unfold make_prop2cnf_ret, make_predata.
      simpl.
      remember (prop2cnf_logic lt' (clist, pcnt, ccnt)) as step1 eqn:Hstep1.
      destruct step1 as [data1 p1'].
      remember (prop2cnf_logic rt' data1) as step2 eqn:Hstep2.
      destruct step2 as [tmp clause_cnt].
      destruct tmp as [cnf_res prop_cnt].
      destruct cnf_res as [cnf_res0 prop_cnt0].
      unfold make_prop2cnf_ret, make_predata in H5, H9.
      rewrite <- H9 in Hstep1.
      inversion Hstep1.
      rewrite H26 in Hstep2.
      rewrite <- H5 in Hstep2.
      inversion Hstep2.
      destruct (p1 ==? p2); try contradiction.
      subst.
      reflexivity.
    }
    unfold prop_cnt_inf.
    unfold prop_cnt_inf in H3.
    pose proof Z.max_lub_l _ _ _ H3.
    pose proof Z.max_lub_r _ _ _ H3.
    unfold make_prop2cnf_ret, make_predata in H5.
    pose proof pcnt_upper_incr _ _ _ _ _ _ _ _ H5.
    apply Z.max_lub; rewrite H_c1, H_c2, H_c3.
    - simpl.
      repeat apply Z.max_lub; try lia.
    - simpl.
      apply Z.abs_le.
      split.
      * 
        repeat apply Z.min_glb; try lia.
      * 
        pose proof Z.le_min_l (Z.min p1 (Z.min (- (pcnt'_2 + 1)) (Z.min 0 0)))
        (Z.min (Z.min p2 (Z.min (- (pcnt'_2 + 1)) (Z.min 0 0)))
           (Z.min (Z.min (- p1) (Z.min (- p2) (Z.min (pcnt'_2 + 1) 0))) (min_cnf clist'_2))).
        pose proof Z.le_min_l p1 (Z.min (- (pcnt'_2 + 1)) (Z.min 0 0)).
        remember ( Z.min (Z.min p1 (Z.min (- (pcnt'_2 + 1)) (Z.min 0 0)))
        (Z.min (Z.min p2 (Z.min (- (pcnt'_2 + 1)) (Z.min 0 0)))
           (Z.min (Z.min (- p1) (Z.min (- p2) (Z.min (pcnt'_2 + 1) 0))) (min_cnf clist'_2)))) as tmp1 eqn:H1000.
        remember (Z.min p1 (Z.min (- (pcnt'_2 + 1)) (Z.min 0 0))) as tmp2 eqn:H2000.
        clear H1000.
        clear H2000.
        lia.
  + remember (- p1 :: pcnt'_2 + 1 :: 0 :: nil) as c1 eqn:H_c1.
    remember (- p2 :: pcnt'_2 + 1 :: 0 :: nil) as c2 eqn:H_c2.
    remember (p1 :: - (pcnt'_2 + 1) :: 0 :: nil) as c3 eqn:H_c3.
    Exists (c1 :: c2 :: c3 :: clist'_2) (pcnt'_2 + 1) (ccnt'_2 + 3) (pcnt'_2 + 1) y0.
    entailer!.
    1: {
      simpl store_SmtProp.
      subst.
      Exists v_2 v.
      simpl.
      entailer!.
    }
    2: {
      repeat rewrite Zlength_cons.
      lia.
    }
    2: {
      unfold make_prop2cnf_ret, make_predata.
      simpl.
      remember (prop2cnf_logic lt' (clist, pcnt, ccnt)) as step1 eqn:Hstep1.
      destruct step1 as [data1 p1'].
      remember (prop2cnf_logic rt' data1) as step2 eqn:Hstep2.
      destruct step2 as [tmp clause_cnt].
      destruct tmp as [cnf_res prop_cnt].
      destruct cnf_res as [cnf_res0 prop_cnt0].
      unfold make_prop2cnf_ret, make_predata in H5, H9.
      rewrite <- H9 in Hstep1.
      inversion Hstep1.
      rewrite H26 in Hstep2.
      rewrite <- H5 in Hstep2.
      inversion Hstep2.
      destruct (p1 ==? p2); try contradiction.
      subst.
      reflexivity.
    }
    unfold prop_cnt_inf.
    unfold prop_cnt_inf in H3.
    pose proof Z.max_lub_l _ _ _ H3.
    pose proof Z.max_lub_r _ _ _ H3.
    unfold make_prop2cnf_ret, make_predata in H5.
    pose proof pcnt_upper_incr _ _ _ _ _ _ _ _ H5.
    apply Z.max_lub; rewrite H_c1, H_c2, H_c3.
    - simpl.
      repeat apply Z.max_lub; try lia.
    - simpl.
      apply Z.abs_le.
      split.
      * 
        repeat apply Z.min_glb; try lia.
      * 
        pose proof Z.le_min_l (Z.min (- p1) (Z.min (pcnt'_2 + 1) (Z.min 0 0)))
        (Z.min (Z.min (- p2) (Z.min (pcnt'_2 + 1) (Z.min 0 0)))
           (Z.min (Z.min p1 (Z.min (- (pcnt'_2 + 1)) (Z.min 0 0))) (min_cnf clist'_2))).
        pose proof Z.le_min_l (- p1) (Z.min (pcnt'_2 + 1) (Z.min 0 0)).
        remember (Z.min (Z.min (- p1) (Z.min (pcnt'_2 + 1) (Z.min 0 0)))
        (Z.min (Z.min (- p2) (Z.min (pcnt'_2 + 1) (Z.min 0 0)))
           (Z.min (Z.min p1 (Z.min (- (pcnt'_2 + 1)) (Z.min 0 0))) (min_cnf clist'_2))) ) as tmp1 eqn:H1000.
        remember (Z.min (- p1) (Z.min (pcnt'_2 + 1) (Z.min 0 0))) as tmp2 eqn:H2000.
        clear H1000.
        clear H2000.
        lia.
  + remember (- p1 :: pcnt'_2 + 1 :: 0 :: nil) as c1 eqn:H_c1.
    remember (- p2 :: pcnt'_2 + 1 :: 0 :: nil) as c2 eqn:H_c2.
    remember (p1 :: p2 :: - (pcnt'_2 + 1) :: nil) as c3 eqn:H_c3.
    Exists (c1 :: c2 :: c3 :: clist'_2) (pcnt'_2 + 1) (ccnt'_2 + 3) (pcnt'_2 + 1) y0.
    entailer!.
    1: {
      simpl store_SmtProp.
      subst.
      Exists v_2 v.
      simpl.
      entailer!.
    }
    2: {
      repeat rewrite Zlength_cons.
      lia.
    }
    2: {
      unfold make_prop2cnf_ret, make_predata.
      simpl.
      remember (prop2cnf_logic lt' (clist, pcnt, ccnt)) as step1 eqn:Hstep1.
      destruct step1 as [data1 p1''].
      remember (prop2cnf_logic rt' data1) as step2 eqn:Hstep2.
      destruct step2 as [tmp clause_cnt].
      destruct tmp as [cnf_res prop_cnt].
      destruct cnf_res as [cnf_res0 prop_cnt0].
      unfold make_prop2cnf_ret, make_predata in H5, H9.
      rewrite <- H9 in Hstep1.
      inversion Hstep1.
      rewrite H26 in Hstep2.
      rewrite <- H5 in Hstep2.
      inversion Hstep2.
      destruct (p1 ==? p2); try contradiction.
      subst.
      reflexivity.
    }
    unfold prop_cnt_inf.
    unfold prop_cnt_inf in H3.
    pose proof Z.max_lub_l _ _ _ H3.
    pose proof Z.max_lub_r _ _ _ H3.
    unfold make_prop2cnf_ret, make_predata in H5.
    pose proof pcnt_upper_incr _ _ _ _ _ _ _ _ H5.
    apply Z.max_lub; rewrite H_c1, H_c2, H_c3.
    - simpl.
      repeat apply Z.max_lub; try lia.
    - simpl.
      apply Z.abs_le.
      split.
      * 
        repeat apply Z.min_glb; try lia.
      * 
        pose proof Z.le_min_l (Z.min (- p1) (Z.min (pcnt'_2 + 1) (Z.min 0 0)))
        (Z.min (Z.min (- p2) (Z.min (pcnt'_2 + 1) (Z.min 0 0)))
           (Z.min (Z.min p1 (Z.min p2 (Z.min (- (pcnt'_2 + 1)) 0))) (min_cnf clist'_2))).
        pose proof Z.le_min_l (- p1) (Z.min (pcnt'_2 + 1) (Z.min 0 0)).
        remember (Z.min (Z.min (- p1) (Z.min (pcnt'_2 + 1) (Z.min 0 0)))
        (Z.min (Z.min (- p2) (Z.min (pcnt'_2 + 1) (Z.min 0 0)))
           (Z.min (Z.min p1 (Z.min p2 (Z.min (- (pcnt'_2 + 1)) 0))) (min_cnf clist'_2)))) as tmp1 eqn:H1000.
        remember (Z.min (- p1) (Z.min (pcnt'_2 + 1) (Z.min 0 0))) as tmp2 eqn:H2000.
        clear H1000.
        clear H2000.
        lia.
  + remember (pcnt'_2 + 1 :: 0 :: 0 :: nil) as c1 eqn:H_c1.
    (* remember (- p2 :: pcnt'_2 + 1 :: 0 :: nil) as c2 eqn:H_c2.
    remember (p1 :: p2 :: - (pcnt'_2 + 1) :: nil) as c3 eqn:H_c3. *)
    Exists (c1 :: clist'_2) (pcnt'_2 + 1) (ccnt'_2 + 1) (pcnt'_2 + 1) y0.
    entailer!.
    1: {
      simpl store_SmtProp.
      subst.
      Exists v_2 v.
      simpl.
      entailer!.
    }
    2: {
      repeat rewrite Zlength_cons.
      lia.
    }
    2: {
      rewrite Zlength_cons, H2.
      lia.
    }
    2: {
      unfold make_prop2cnf_ret, make_predata.
      simpl.
      remember (prop2cnf_logic lt' (clist, pcnt, ccnt)) as step1 eqn:Hstep1.
      destruct step1 as [data1 p1'].
      remember (prop2cnf_logic rt' data1) as step2 eqn:Hstep2.
      destruct step2 as [tmp clause_cnt].
      destruct tmp as [cnf_res prop_cnt].
      destruct cnf_res as [cnf_res0 prop_cnt0].
      unfold make_prop2cnf_ret, make_predata in H5, H9.
      rewrite <- H9 in Hstep1.
      inversion Hstep1.
      rewrite H26 in Hstep2.
      rewrite <- H5 in Hstep2.
      inversion Hstep2.
      destruct (p1 ==? p2); try contradiction.
      subst.
      reflexivity.
    }
    unfold prop_cnt_inf.
    unfold prop_cnt_inf in H3.
    pose proof Z.max_lub_l _ _ _ H3.
    pose proof Z.max_lub_r _ _ _ H3.
    unfold make_prop2cnf_ret, make_predata in H5.
    pose proof pcnt_upper_incr _ _ _ _ _ _ _ _ H5.
    apply Z.max_lub; rewrite H_c1.
    - simpl.
      repeat apply Z.max_lub; try lia.
    - simpl.
      apply Z.abs_le.
      split.
      * 
        repeat apply Z.min_glb; try lia.
      * 
        pose proof Z.le_min_r (Z.min (pcnt'_2 + 1) (Z.min 0 (Z.min 0 0))) (min_cnf clist'_2).
        remember (Z.min (Z.min (pcnt'_2 + 1) (Z.min 0 (Z.min 0 0))) (min_cnf clist'_2)) as tmp1 eqn:H1000.
        clear H1000.
        lia.
  + remember (p1 :: pcnt'_2 + 1 :: 0 :: nil) as c1 eqn:H_c1.
    remember (- p2 :: pcnt'_2 + 1 :: 0 :: nil) as c2 eqn:H_c2.
    remember (- p1 :: p2 :: - (pcnt'_2 + 1) :: nil) as c3 eqn:H_c3.
    Exists (c1 :: c2 :: c3 :: clist'_2) (pcnt'_2 + 1) (ccnt'_2 + 3) (pcnt'_2 + 1) y0.
    entailer!.
    1: {
      simpl store_SmtProp.
      subst.
      Exists v_2 v.
      simpl.
      entailer!.
    }
    2: {
      repeat rewrite Zlength_cons.
      rewrite H2.
      lia.
    }
    2: {
      repeat rewrite Zlength_cons.
      lia.
    }
    2: {
      unfold make_prop2cnf_ret, make_predata.
      simpl.
      remember (prop2cnf_logic lt' (clist, pcnt, ccnt)) as step1 eqn:Hstep1.
      destruct step1 as [data1 p1'].
      remember (prop2cnf_logic rt' data1) as step2 eqn:Hstep2.
      destruct step2 as [tmp clause_cnt].
      destruct tmp as [cnf_res prop_cnt].
      destruct cnf_res as [cnf_res0 prop_cnt0].
      unfold make_prop2cnf_ret, make_predata in H5, H9.
      rewrite <- H9 in Hstep1.
      inversion Hstep1.
      rewrite H26 in Hstep2.
      rewrite <- H5 in Hstep2.
      inversion Hstep2.
      destruct (p1 ==? p2); try contradiction.
      subst.
      reflexivity.
    }
    unfold prop_cnt_inf.
    unfold prop_cnt_inf in H3.
    pose proof Z.max_lub_l _ _ _ H3.
    pose proof Z.max_lub_r _ _ _ H3.
    unfold make_prop2cnf_ret, make_predata in H5.
    pose proof pcnt_upper_incr _ _ _ _ _ _ _ _ H5.
    apply Z.max_lub; rewrite H_c1, H_c2, H_c3.
    - simpl.
      repeat apply Z.max_lub; try lia.
    - simpl.
      apply Z.abs_le.
      split.
      * 
        repeat apply Z.min_glb; try lia.
      * 
        pose proof Z.le_min_l (Z.min p1 (Z.min (pcnt'_2 + 1) (Z.min 0 0)))
        (Z.min (Z.min (- p2) (Z.min (pcnt'_2 + 1) (Z.min 0 0)))
           (Z.min (Z.min (- p1) (Z.min p2 (Z.min (- (pcnt'_2 + 1)) 0))) (min_cnf clist'_2))).
        pose proof Z.le_min_l p1 (Z.min (pcnt'_2 + 1) (Z.min 0 0)).
        remember (Z.min (Z.min p1 (Z.min (pcnt'_2 + 1) (Z.min 0 0)))
        (Z.min (Z.min (- p2) (Z.min (pcnt'_2 + 1) (Z.min 0 0)))
           (Z.min (Z.min (- p1) (Z.min p2 (Z.min (- (pcnt'_2 + 1)) 0))) (min_cnf clist'_2)))) as tmp1 eqn:H1000.
        remember (Z.min p1 (Z.min (pcnt'_2 + 1) (Z.min 0 0))) as tmp2 eqn:H2000.
        clear H1000.
        clear H2000.
        lia.
  + remember (pcnt'_2 + 1 :: 0 :: 0 :: nil) as c1 eqn:H_c1.
    (* remember (- p2 :: pcnt'_2 + 1 :: 0 :: nil) as c2 eqn:H_c2.
    remember (- p1 :: p2 :: - (pcnt'_2 + 1) :: nil) as c3 eqn:H_c3. *)
    Exists (c1 :: clist'_2) (pcnt'_2 + 1) (ccnt'_2 + 1) (pcnt'_2 + 1) y0.
    entailer!.
    1: {
      simpl store_SmtProp.
      subst.
      Exists v_2 v.
      simpl.
      entailer!.
    }
    2: {
      repeat rewrite Zlength_cons.
      lia.
    }
    2: {
      repeat rewrite Zlength_cons.
      rewrite H2.
      lia.
    }
    2: {
      unfold make_prop2cnf_ret, make_predata.
      simpl.
      remember (prop2cnf_logic lt' (clist, pcnt, ccnt)) as step1 eqn:Hstep1.
      destruct step1 as [data1 p1'].
      remember (prop2cnf_logic rt' data1) as step2 eqn:Hstep2.
      destruct step2 as [tmp clause_cnt].
      destruct tmp as [cnf_res prop_cnt].
      destruct cnf_res as [cnf_res0 prop_cnt0].
      unfold make_prop2cnf_ret, make_predata in H5, H9.
      rewrite <- H9 in Hstep1.
      inversion Hstep1.
      rewrite H26 in Hstep2.
      rewrite <- H5 in Hstep2.
      inversion Hstep2.
      destruct (p1 ==? p2); try contradiction.
      subst.
      reflexivity.
    }
    unfold prop_cnt_inf.
    unfold prop_cnt_inf in H3.
    pose proof Z.max_lub_l _ _ _ H3.
    pose proof Z.max_lub_r _ _ _ H3.
    unfold make_prop2cnf_ret, make_predata in H5.
    pose proof pcnt_upper_incr _ _ _ _ _ _ _ _ H5.
    apply Z.max_lub; rewrite H_c1.
    - simpl.
      repeat apply Z.max_lub; try lia.
    - simpl.
      apply Z.abs_le.
      split.
      * 
        repeat apply Z.min_glb; try lia.
      * 
        pose proof Z.le_min_r (Z.min (pcnt'_2 + 1) (Z.min 0 (Z.min 0 0))) (min_cnf clist'_2).
        remember (Z.min (Z.min (pcnt'_2 + 1) (Z.min 0 (Z.min 0 0))) (min_cnf clist'_2)) as tmp1 eqn:H1000.
        clear H1000.
        lia.
  + remember (p1 :: p2 :: pcnt'_2 + 1 :: nil) as c1 eqn:H_c1.
    remember (- p1 :: - p2 :: pcnt'_2 + 1 :: nil) as c2 eqn:H_c2.
    remember (p1 :: - p2 :: - (pcnt'_2 + 1) :: nil) as c3 eqn:H_c3.
    remember (- p1 :: p2 :: - (pcnt'_2 + 1) :: nil) as c4 eqn:H_c4.
    Exists (c1 :: c2 :: c3 :: c4 :: clist'_2) (pcnt'_2 + 1) (ccnt'_2 + 4) (pcnt'_2 + 1) y0.
    entailer!.
    1: {
      simpl store_SmtProp.
      subst.
      Exists v_2 v.
      simpl.
      entailer!.
    }
    2: {
      repeat rewrite Zlength_cons.
      lia.
    }
    2: {
      repeat rewrite Zlength_cons.
      rewrite H2.
      lia.
    }
    2: {
      unfold make_prop2cnf_ret, make_predata.
      simpl.
      remember (prop2cnf_logic lt' (clist, pcnt, ccnt)) as step1 eqn:Hstep1.
      destruct step1 as [data1 p1'].
      remember (prop2cnf_logic rt' data1) as step2 eqn:Hstep2.
      destruct step2 as [tmp clause_cnt].
      destruct tmp as [cnf_res prop_cnt].
      destruct cnf_res as [cnf_res0 prop_cnt0].
      unfold make_prop2cnf_ret, make_predata in H5, H9.
      rewrite <- H9 in Hstep1.
      inversion Hstep1.
      rewrite H26 in Hstep2.
      rewrite <- H5 in Hstep2.
      inversion Hstep2.
      destruct (p1 ==? p2); try contradiction.
      subst.
      reflexivity.
    }
    unfold prop_cnt_inf.
    unfold prop_cnt_inf in H3.
    pose proof Z.max_lub_l _ _ _ H3.
    pose proof Z.max_lub_r _ _ _ H3.
    unfold make_prop2cnf_ret, make_predata in H5.
    pose proof pcnt_upper_incr _ _ _ _ _ _ _ _ H5.
    apply Z.max_lub; rewrite H_c1, H_c2, H_c3, H_c4.
    - simpl.
      repeat apply Z.max_lub; try lia.
    - simpl.
      apply Z.abs_le.
      split.
      * 
        repeat apply Z.min_glb; try lia.
      * 
        pose proof Z.le_min_l (Z.min p1 (Z.min p2 (Z.min (pcnt'_2 + 1) 0)))
        (Z.min (Z.min (- p1) (Z.min (- p2) (Z.min (pcnt'_2 + 1) 0)))
           (Z.min (Z.min p1 (Z.min (- p2) (Z.min (- (pcnt'_2 + 1)) 0)))
              (Z.min (Z.min (- p1) (Z.min p2 (Z.min (- (pcnt'_2 + 1)) 0))) (min_cnf clist'_2)))) .
        pose proof Z.le_min_l p1 (Z.min p2 (Z.min (pcnt'_2 + 1) 0)).
        remember (Z.min (Z.min p1 (Z.min p2 (Z.min (pcnt'_2 + 1) 0)))
        (Z.min (Z.min (- p1) (Z.min (- p2) (Z.min (pcnt'_2 + 1) 0)))
           (Z.min (Z.min p1 (Z.min (- p2) (Z.min (- (pcnt'_2 + 1)) 0)))
              (Z.min (Z.min (- p1) (Z.min p2 (Z.min (- (pcnt'_2 + 1)) 0))) (min_cnf clist'_2)))) ) as tmp1 eqn:H1000.
        remember (Z.min p1 (Z.min p2 (Z.min (pcnt'_2 + 1) 0))) as tmp2 eqn:H2000.
        clear H1000.
        clear H2000.
        lia.
Qed.

Lemma proof_of_prop2cnf_partial_solve_wit_2_pure : prop2cnf_partial_solve_wit_2_pure.
Proof.
  pre_process.
Qed.

Lemma proof_of_prop2cnf_partial_solve_wit_20_pure : prop2cnf_partial_solve_wit_20_pure.
Proof.
  pre_process.
Qed.

Lemma proof_of_prop2cnf_partial_solve_wit_19_pure : prop2cnf_partial_solve_wit_19_pure.
Proof.
  pre_process.
  rewrite PreH27 in *.
  unfold make_predata, make_prop2cnf_ret in PreH11.
  pose proof pcnt_upper_incr _ _ _ _ _ _ _ _ PreH11.
  assert (p1 <= pcnt'_2 + 1) by lia.
  assert (- p1 <= pcnt'_2 + 1) by lia.
  entailer!.
Qed.

Lemma proof_of_prop2cnf_partial_solve_wit_34_pure : prop2cnf_partial_solve_wit_34_pure.
Proof.
  pre_process.
Qed.

Lemma proof_of_prop2cnf_which_implies_wit_1 : prop2cnf_which_implies_wit_1.
Proof.
  pre_process.
  sep_apply store_SmtProp_unfold.
  Exists (SmtPTID prop).
  entailer!.
Qed. 

Lemma proof_of_prop2cnf_which_implies_wit_2 : prop2cnf_which_implies_wit_2.
Proof.
  pre_process.
  rewrite PreH2.
  rewrite <- PreH1, PreH2.
  sep_apply store_SmtProp'_Binary.
  Intros op lt rt y z.
  Exists z y op lt rt.
  entailer!.
  lia.
Qed. 

Lemma proof_of_prop2cnf_which_implies_wit_3 : prop2cnf_which_implies_wit_3.
Proof.
  pre_process.
  rewrite PreH2 in PreH1.
  pose proof prop_cnt_inf_Binary_l _ _ _ _ PreH1.
  pose proof prop_cnt_inf_Binary_r _ _ _ _ PreH1.
  entailer!.
Qed.

Lemma proof_of_prop2cnf_which_implies_wit_4 : prop2cnf_which_implies_wit_4.
Proof.
  pre_process.
  rewrite PreH2 in PreH1.
  simpl in PreH1.
  pose proof SmtProp_size_nonneg lt.
  pose proof SmtProp_size_nonneg rt.
  assert (SmtProp_size lt <= 10000) by lia.
  assert (SmtProp_size rt <= 10000) by lia.
  entailer!.
Qed.

Lemma proof_of_prop2cnf_which_implies_wit_5 : prop2cnf_which_implies_wit_5.
Proof.
  pre_process.
  rewrite PreH2 in PreH1.
  simpl in PreH1.
  pose proof SmtProp_size_nonneg lt.
  pose proof SmtProp_size_nonneg rt.
  assert (Zlength clist <= 40000 - 4 * SmtProp_size lt) by lia.
  entailer!.
Qed.

Lemma proof_of_prop2cnf_which_implies_wit_6 : prop2cnf_which_implies_wit_6.
Proof.
  pre_process.
  rewrite PreH2 in *.
  simpl in PreH1.
  pose proof SmtProp_size_nonneg lt.
  pose proof SmtProp_size_nonneg rt.
  assert (pcnt <= 40000 - SmtProp_size lt) by lia.
  entailer!.
Qed.

Lemma proof_of_prop2cnf_which_implies_wit_7 : prop2cnf_which_implies_wit_7.
Proof.
  pre_process.
  rewrite PreH3 in *.
  simpl in PreH2.
  pose proof SmtProp_size_nonneg lt.
  pose proof SmtProp_size_nonneg rt.
  assert (Zlength clist' <= 40000 - 4 * SmtProp_size rt) by lia.
  entailer!.
Qed.

Lemma proof_of_prop2cnf_which_implies_wit_8 : prop2cnf_which_implies_wit_8.
Proof.
  pre_process.
  unfold make_predata, make_prop2cnf_ret in PreH1.
  pose proof pcnt_upper_incr _ _ _ _ _ _ _ _ PreH1.
  assert (prop_cnt_inf_SmtProp rt <= pcnt') by lia.
  entailer!.
Qed.

Lemma proof_of_prop2cnf_which_implies_wit_9 : prop2cnf_which_implies_wit_9.
Proof.
  pre_process.
  rewrite PreH3 in *.
  simpl in PreH2.
  pose proof SmtProp_size_nonneg lt.
  assert (pcnt' <= 39999 - SmtProp_size rt) by lia.
  entailer!.
Qed. 

Lemma proof_of_prop2cnf_which_implies_wit_10 : prop2cnf_which_implies_wit_10.
Proof.
  pre_process.
  unfold store_predata.
  Intros y.
  Exists y.
  entailer!.
  pose proof prop_cnt_nneg clist'_2.
  lia.
Qed. 

Lemma proof_of_prop2cnf_which_implies_wit_11 : prop2cnf_which_implies_wit_11.
Proof.
  pre_process.
  rewrite PreH4 in *.
  simpl in PreH3.
  simpl.
  pose proof SmtProp_size_nonneg lt'.
  pose proof SmtProp_size_nonneg rt'.
  assert (pcnt'_2 <= pcnt + (1 + SmtProp_size lt' + SmtProp_size rt') - 1) by lia.
  assert (pcnt'_2 <= 39999) by lia.
  entailer!.
Qed.

Lemma proof_of_prop2cnf_which_implies_wit_13 : prop2cnf_which_implies_wit_13.
Proof.
  pre_process.
  unfold store_predata.
  Exists y''.
  entailer!.
Qed.

Lemma proof_of_prop2cnf_which_implies_wit_15 : prop2cnf_which_implies_wit_15.
Proof.
  pre_process.
  rewrite PreH3.
  simpl.
  assert (Zlength clist'_2 <= Zlength clist + 4 * (1 + SmtProp_size lt' + SmtProp_size rt') - 4) by lia.
  entailer!.
Qed.

Lemma proof_of_prop2cnf_which_implies_wit_17 : prop2cnf_which_implies_wit_17.
Proof.
  pre_process.
  rewrite PreH2.
  rewrite <- PreH1, PreH2.
  sep_apply store_SmtProp'_Unary.
  Intros op prop0 y.
  Exists y op prop0.
  entailer!.
  lia.
Qed. 


Lemma proof_of_prop2cnf_which_implies_wit_18 : prop2cnf_which_implies_wit_18.
Proof.
  pre_process.
  rewrite PreH2 in PreH1.
  pose proof prop_cnt_inf_Unary_r _ _ _ PreH1.
  entailer!.
Qed.


Lemma proof_of_prop2cnf_which_implies_wit_19 : prop2cnf_which_implies_wit_19.
Proof.
  pre_process.
  rewrite PreH2 in PreH1.
  simpl in PreH1.
  assert (SmtProp_size sub_prop <= 10000) by lia.
  entailer!.
Qed.

Lemma proof_of_prop2cnf_which_implies_wit_20 : prop2cnf_which_implies_wit_20.
Proof.
  pre_process.
  rewrite PreH2 in PreH1.
  simpl in PreH1.
  pose proof SmtProp_size_nonneg sub_prop.
  assert (Zlength clist <= 40000 - 4 * SmtProp_size sub_prop) by lia.
  entailer!.
Qed.

Lemma proof_of_prop2cnf_which_implies_wit_21 : prop2cnf_which_implies_wit_21.
Proof.
  pre_process.
  rewrite PreH2 in *.
  simpl in PreH1.
  pose proof SmtProp_size_nonneg sub_prop.
  assert (pcnt <= 40000 - SmtProp_size sub_prop) by lia.
  entailer!.
Qed.

Lemma proof_of_prop2cnf_which_implies_wit_22 : prop2cnf_which_implies_wit_22.
Proof.
  pre_process.
  unfold store_predata.
  Intros y.
  Exists y.
  entailer!.
  pose proof prop_cnt_nneg clist'.
  lia.
Qed.

Lemma proof_of_prop2cnf_which_implies_wit_23 : prop2cnf_which_implies_wit_23.
Proof.
  pre_process.
  rewrite PreH3 in *.
  simpl in PreH2.
  simpl.
  pose proof SmtProp_size_nonneg sub_prop'.
  assert (pcnt' <= pcnt + (1 + SmtProp_size sub_prop') - 1) by lia.
  assert (pcnt' <= 39999) by lia.
  entailer!.
Qed.

Lemma proof_of_prop2cnf_which_implies_wit_25 : prop2cnf_which_implies_wit_25.
Proof.
  pre_process.
  unfold store_predata.
  Exists y''.
  entailer!.
Qed.


Lemma proof_of_prop2cnf_which_implies_wit_27 : prop2cnf_which_implies_wit_27.
Proof.
  pre_process.
  rewrite PreH2.
  simpl.
  assert (Zlength clist' <= Zlength clist + 4 * (1 + SmtProp_size sub_prop') - 4) by lia.
  entailer!.
Qed.

Lemma proof_of_prop2cnf_which_implies_wit_29 : prop2cnf_which_implies_wit_29.
Proof.
  pre_process.
  rewrite PreH1.
  rewrite <- PreH2, PreH1.
  sep_apply store_SmtProp'_Var.
  Intros var.
  Exists var.
  entailer!.
  lia.
Qed.
