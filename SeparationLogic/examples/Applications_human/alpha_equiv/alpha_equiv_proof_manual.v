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
From SimpleC.EE.Applications_human.alpha_equiv Require Import alpha_equiv_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
From SimpleC.EE.QCP_demos_human Require Import sll_merge_rel_lib.
Local Open Scope monad.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap relations.
From FP Require Import PartialOrder_Setoid BourbakiWitt.
From SimpleC.EE.Applications_human.alpha_equiv Require Import ast_lib.
From SimpleC.EE.Applications_human Require Import malloc.
From SimpleC.EE.Applications_human Require Import super_poly_sll2.
Local Open Scope sac.

Lemma proof_of_alpha_equiv_safety_wit_16 : alpha_equiv_safety_wit_16.
Proof. 
  pre_process.
  unfold termtypeID in *.
  destruct term1; lia.
Qed.

Lemma proof_of_alpha_equiv_return_wit_15 : alpha_equiv_return_wit_15.
Proof. 
  pre_process.
  rewrite PreH1.
  apply store_null_right.
Qed.

Lemma proof_of_alpha_equiv_return_wit_14 : alpha_equiv_return_wit_14.
Proof.
  pre_process.
  rewrite PreH1.
  apply store_null_left.
Qed.

Lemma proof_of_alpha_equiv_return_wit_13 : alpha_equiv_return_wit_13.
Proof.
  pre_process.
  entailer!.
  2: {
    destruct term1; destruct term2; simpl in PreH1; try lia.
    all: unfold term_alpha_eqn, term_alpha_eq; reflexivity.
  }
  pose proof (store_term_fold_out t2_pre term2 PreH3) as Hfold2.
  sep_apply Hfold2.
  pose proof (store_term_fold_out t1_pre term1 PreH2) as Hfold1.
  sep_apply Hfold1.
  entailer!.
Qed.

Lemma proof_of_alpha_equiv_return_wit_12 : alpha_equiv_return_wit_12.
Proof.
  pre_process.
  rewrite PreH1 in PreH2.
  unfold list_Z_cmp in PreH2.
  destruct (list_Z_eqb str1 str2) eqn:Heq; [ | discriminate ].
  unfold store_term, term_alpha_eqn, term_alpha_eq.
  rewrite PreH5, PreH6.
  Exists y z.
  entailer!.
  rewrite Heq.
  reflexivity.
Qed.

Lemma proof_of_alpha_equiv_return_wit_11 : alpha_equiv_return_wit_11.
Proof.
  pre_process.
  unfold list_Z_cmp in PreH2.
  destruct (list_Z_eqb str1 str2) eqn:Heq; [ subst retval; contradiction | ].
  unfold store_term, term_alpha_eqn, term_alpha_eq.
  rewrite PreH5, PreH6.
  Exists y z.
  entailer!.
  rewrite Heq.
  reflexivity.
Qed.

Lemma proof_of_alpha_equiv_return_wit_10 : alpha_equiv_return_wit_10.
Proof.
  pre_process.
  unfold store_term, term_alpha_eqn, term_alpha_eq.
  rewrite PreH4, PreH5.
  entailer!.
  destruct (ctID typ1 =? ctID typ2)%Z eqn:E.
  + apply Z.eqb_eq in E.
    contradiction.
  + reflexivity.
Qed.

Lemma proof_of_alpha_equiv_return_wit_9 : alpha_equiv_return_wit_9.
Proof. 
  pre_process.
  unfold store_term.
  rewrite PreH6, PreH7.
  entailer!.
  unfold term_alpha_eqn, term_alpha_eq.
  rewrite PreH3 at 1.
  rewrite Z.eqb_refl.
  rewrite PreH1.
  rewrite Z.eqb_refl.
  rewrite PreH2.
  reflexivity.
Qed.

Lemma proof_of_alpha_equiv_return_wit_8 : alpha_equiv_return_wit_8.
Proof.
  pre_process.
  unfold store_term.
  rewrite PreH6, PreH7.
  entailer!.
  unfold term_alpha_eqn, term_alpha_eq.
  rewrite PreH3 at 1.
  rewrite Z.eqb_refl.
  destruct (con1 =? con2)%Z eqn:E.
  + apply Z.eqb_eq in E.
    congruence.
  + rewrite PreH2.
    reflexivity.
Qed.

Lemma proof_of_alpha_equiv_return_wit_7 : alpha_equiv_return_wit_7.
Proof.
  pre_process.
  unfold store_term.
  rewrite PreH5, PreH6.
  entailer!.
  unfold term_alpha_eqn, term_alpha_eq.
  rewrite PreH2 at 1.
  rewrite Z.eqb_refl.
  destruct (con1 =? con2)%Z eqn:E.
  + unfold negb.
    destruct (ctID typ1 =? 0)%Z eqn:Eq; [ | reflexivity].
    apply Z.eqb_eq in E, Eq.
    contradiction.
  + unfold negb.
    apply Z.eqb_neq in E.
    destruct (ctID typ1 =? 0)%Z eqn:Eq; [ | reflexivity].
    apply Z.eqb_eq in Eq.
    contradiction.
Qed.  

Lemma proof_of_alpha_equiv_return_wit_6 : alpha_equiv_return_wit_6.
Proof.
  pre_process.
  unfold store_term.
  rewrite PreH7, PreH8.
  fold store_term.
  Exists y1 z1 y2 z2.
  entailer!.
  unfold term_alpha_eqn in *.
  unfold term_alpha_eq.
  fold term_alpha_eq.
  destruct (term_alpha_eq lt1 lt2) eqn:Eql; [ | reflexivity].
  destruct (term_alpha_eq rt1 rt2) eqn:Eqr; [ | reflexivity].
  lia.
Qed.

Lemma proof_of_alpha_equiv_return_wit_5 : alpha_equiv_return_wit_5.
Proof.
  pre_process.
  unfold store_term.
  rewrite PreH7, PreH8.
  fold store_term.
  Exists y1 z1 y2 z2.
  entailer!.
  unfold term_alpha_eqn in *.
  unfold term_alpha_eq.
  fold term_alpha_eq.
  destruct (term_alpha_eq rt1 rt2) eqn:Eqr; [ | contradiction].
  destruct (term_alpha_eq lt1 lt2) eqn:Eql; [ | contradiction].
  reflexivity.
Qed.

Lemma proof_of_alpha_equiv_return_wit_4 : alpha_equiv_return_wit_4.
Proof.
  pre_process.
  unfold store_term.
  rewrite PreH5, PreH6.
  fold store_term.
  Exists y1 z1 y2 z2.
  entailer!.
  unfold term_alpha_eqn in *.
  unfold term_alpha_eq.
  fold term_alpha_eq.
  destruct (term_alpha_eq lt1 lt2) eqn:Eql; [ simpl in PreH2; lia | reflexivity].
Qed.

Lemma proof_of_alpha_equiv_return_wit_3 : alpha_equiv_return_wit_3.
Proof.
  pre_process.
  unfold store_term.
  rewrite PreH4, PreH5.
  fold store_term.
  Exists y1 z1 y2 z2.
  entailer!.
  unfold term_alpha_eqn in *.
  unfold term_alpha_eq.
  fold term_alpha_eq.
  destruct (qtID qt1 =? qtID qt2)%Z eqn:Eq; [ | reflexivity].
  apply Z.eqb_eq in Eq.
  congruence.
Qed.

Lemma proof_of_alpha_equiv_return_wit_2 : alpha_equiv_return_wit_2.
Proof.
  pre_process.
  unfold store_term.
  rewrite PreH7, PreH8.
  fold store_term.
  Exists y1 z1 y2 z2.
  entailer!.
  unfold term_alpha_eqn in *.
  unfold term_alpha_eq.
  fold term_alpha_eq.
  rewrite PreH2 in PreH3. 
  unfold list_Z_cmp in PreH3.
  destruct (qtID qt1 =? qtID qt2)%Z eqn:Eq.
  + destruct (list_Z_eqb qv1 qv2) eqn:vEq; [ | congruence].
    pose proof list_Z_eqb2eq qv1 qv2 vEq as vvEq.
    pose proof (term_subst_v_same_name qv1 qv2 qterm2 vvEq) as qtEq.
    rewrite qtEq.
    tauto.
  + destruct (list_Z_eqb qv1 qv2) eqn:vEq; [ | congruence].
    rewrite Z.eqb_neq in Eq.
    congruence.
Qed.

Lemma proof_of_alpha_equiv_return_wit_1 : alpha_equiv_return_wit_1.
Proof.
  pre_process.
  unfold store_term.
  rewrite PreH11, PreH12.
  fold store_term.
  Exists y1 z1 y2 z2.
  entailer!.  
  unfold term_alpha_eqn in *.
  unfold term_alpha_eq.
  fold term_alpha_eq.
  destruct (qtID qt1 =? qtID qt2)%Z eqn:Eq.
  + auto.
  + rewrite Z.eqb_neq in Eq.
    congruence.
Qed.


Lemma proof_of_alpha_equiv_which_implies_wit_1 : alpha_equiv_which_implies_wit_1.
Proof. 
  pre_process.
  sep_apply store_term_unfold.
  sep_apply store_term_unfold.
  unfold NULL.
  entailer!.
Qed.
   
Lemma proof_of_alpha_equiv_which_implies_wit_2 : alpha_equiv_which_implies_wit_2.
Proof. 
  pre_process.
  sep_apply store_term'_Var; unfold NULL.
  Intros v1 y1.
  sep_apply store_term'_Var; unfold NULL.
  Intros v2 y2.
  Exists y2 y1 v2 v1.
  entailer!.
  + auto.
  + lia.
  + auto.
  + auto.
Qed.  

Lemma proof_of_alpha_equiv_which_implies_wit_3 : alpha_equiv_which_implies_wit_3.
Proof. 
  pre_process. 
  sep_apply store_term'_Const; unfold NULL.
  Intros ty1 c1.
  sep_apply store_term'_Const; unfold NULL.
  Intros ty2 c2.
  Exists ty2 c2 ty1 c1.
  entailer!.
  + auto.
  + lia.
  + auto.
  + auto.
Qed. 

Lemma proof_of_alpha_equiv_which_implies_wit_4 : alpha_equiv_which_implies_wit_4.
Proof. 
  pre_process.
  sep_apply store_term'_Apply; unfold NULL.
  Intros ltt1 rtt1 yy1 zz1.
  sep_apply store_term'_Apply; unfold NULL.
  Intros ltt2 rtt2 yy2 zz2.
  Exists zz2 zz1 yy2 yy1.
  Exists ltt2 rtt2 ltt1 rtt1.
  entailer!.
  + auto.
  + lia.
  + auto.
  + auto.
Qed. 

Lemma proof_of_alpha_equiv_which_implies_wit_5 : alpha_equiv_which_implies_wit_5.
Proof.  
  pre_process.
  sep_apply store_term'_Quant; unfold NULL.
  Intros qtt1 qvv1 bb1 yy1 zz1.
  sep_apply store_term'_Quant; unfold NULL.
  Intros qtt2 qvv2 bb2 yy2 zz2.
  Exists zz2 zz1 yy2 yy1.
  Exists qtt2 qvv2 bb2.
  Exists qtt1 qvv1 bb1.
  entailer!.
  + auto.
  + lia.
  + auto.
  + auto.
Qed. 

Lemma proof_of_alpha_equiv_which_implies_wit_6 : alpha_equiv_which_implies_wit_6.
Proof. 
  pre_process.
  unfold store_string.
  unfold NULL.
  Intros x n.
  Exists x n.
  entailer!.
Qed. 
