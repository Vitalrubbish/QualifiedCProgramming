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
From SimpleC.EE.Applications_human.alpha_equiv Require Import subst_goal.
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

Lemma proof_of_subst_var_safety_wit_5 : subst_var_safety_wit_5.
Proof. 
    pre_process.
    unfold termtypeID in *.
    destruct trm; lia.
Qed.

Lemma proof_of_subst_var_return_wit_6 : subst_var_return_wit_6.
Proof.    
    pre_process.
    unfold list_Z_cmp in PreH1.
    rewrite PreH12 in PreH1.
    destruct (list_Z_eqb qvar src_str) eqn:Heq; [ | discriminate ].
    unfold term_subst_v.
    rewrite PreH3, Heq.
    unfold store_term.
    simpl.
    Exists y z.
    entailer!.
Qed.  

Lemma proof_of_subst_var_return_wit_5 : subst_var_return_wit_5.
Proof. 
    pre_process.
    unfold list_Z_cmp in PreH2.
    destruct (list_Z_eqb qvar src_str) eqn:Heq; [ rewrite PreH2 in PreH13; contradiction | ].
    unfold term_subst_v.
    rewrite PreH4, Heq.
    unfold store_term.
    simpl.
    rewrite PreH1 in *.
    Exists y z.
    entailer!.
Qed.

Lemma proof_of_subst_var_return_wit_4 : subst_var_return_wit_4.
Proof. 
    pre_process.
    unfold term_subst_v.
    rewrite PreH4.
    unfold store_term.
    simpl.
    rewrite PreH1 in *.
    rewrite PreH2 in *.
    Exists y z.
    entailer!.
Qed. 

Lemma proof_of_subst_var_return_wit_3 : subst_var_return_wit_3.
Proof.
    pre_process.
    unfold term_subst_v.
    rewrite PreH2.
    unfold store_term.
    simpl.
    entailer!.
Qed. 

Lemma proof_of_subst_var_return_wit_2 : subst_var_return_wit_2.
Proof. 
    pre_process.
    unfold list_Z_cmp in PreH2.
    destruct (list_Z_eqb var src_str) eqn:Heq; [ rewrite PreH2 in PreH1; contradiction | ].
    unfold term_subst_v.
    rewrite PreH4, Heq.
    unfold store_term.
    simpl.
    fold term_subst_v.
    fold store_term.
    Exists y.
    entailer!.
Qed.

Lemma proof_of_subst_var_return_wit_1 : subst_var_return_wit_1.
Proof.
    pre_process.
    unfold list_Z_cmp in PreH3.
    rewrite PreH2 in PreH3.
    destruct (list_Z_eqb var src_str) eqn:Heq; [ | discriminate ].
    unfold term_subst_v.
    rewrite PreH5, Heq.
    unfold store_term.
    simpl.
    fold store_term.
    Exists retval_2.
    entailer!.
Qed.
    
Lemma proof_of_subst_var_partial_solve_wit_4_pure : subst_var_partial_solve_wit_4_pure.
Proof.
    pre_process.
    unfold store_string.
    Intros n1 n2 n3.
    entailer!.
Qed.
    
Lemma proof_of_subst_var_partial_solve_wit_8_pure : subst_var_partial_solve_wit_8_pure.
Proof. 
    pre_process.
    unfold store_string.
    Intros n1 n2.
    sep_apply store_term_unfold.
    entailer!.
Qed.

Lemma proof_of_subst_var_partial_solve_wit_9_pure : subst_var_partial_solve_wit_9_pure.
Proof.
    pre_process.
    unfold store_string.
    Intros n1 n2.
    sep_apply store_term_unfold.
    entailer!.
Qed.
    
Lemma proof_of_subst_var_partial_solve_wit_12_pure : subst_var_partial_solve_wit_12_pure.
Proof.
    pre_process.
    unfold store_string.
    Intros n1 n2 n3.
    sep_apply (store_term_unfold z qterm).
    entailer!.
Qed.

Lemma proof_of_subst_var_which_implies_wit_1 : subst_var_which_implies_wit_1.
Proof. 
    pre_process.
    sep_apply store_term_unfold.
    entailer!.
Qed.

Lemma proof_of_subst_var_which_implies_wit_2 : subst_var_which_implies_wit_2.
Proof.
    pre_process.
    sep_apply store_term'_Var; [ | tauto | tauto].
    Intros var y.
    Exists y var.
    entailer!.
Qed. 

Lemma proof_of_subst_var_which_implies_wit_3 : subst_var_which_implies_wit_3.
Proof. 
    pre_process.
    sep_apply store_term'_Const; [ | tauto | tauto].
    Intros y z.
    Exists y z.
    entailer!.
Qed. 

Lemma proof_of_subst_var_which_implies_wit_4 : subst_var_which_implies_wit_4.
Proof. 
    pre_process.
    sep_apply store_term'_Apply; [ | tauto | tauto].
    Intros lt rt y z.
    Exists z y lt rt.
    entailer!.
Qed.

Lemma proof_of_subst_var_which_implies_wit_5 : subst_var_which_implies_wit_5.
Proof. 
    pre_process.
    sep_apply store_term'_Quant; [ | tauto | tauto].
    Intros typ v b y z.
    Exists z y typ v b.
    entailer!.
Qed. 

Lemma proof_of_subst_term_safety_wit_5 : subst_term_safety_wit_5.
Proof. 
    pre_process. 
    unfold termtypeID in *.
    destruct trm; lia.
Qed.

Lemma proof_of_subst_term_return_wit_6 : subst_term_return_wit_6.
Proof. 
    pre_process.
    unfold list_Z_cmp in PreH1.
    rewrite PreH12 in PreH1.
    destruct (list_Z_eqb qvar src_str) eqn:Heq; [ | discriminate ].
    unfold term_subst_t.
    rewrite PreH3, Heq.
    unfold store_term.
    simpl.
    Exists y z.
    entailer!.
Qed.

Lemma proof_of_subst_term_return_wit_5 : subst_term_return_wit_5.
Proof.  
    pre_process.
    unfold list_Z_cmp in PreH1.
    destruct (list_Z_eqb qvar src_str) eqn:Heq; [ rewrite PreH1 in PreH12; contradiction | ].
    unfold term_subst_t.
    rewrite PreH3, Heq.
    unfold store_term.
    simpl.
    Exists y retval_2.
    entailer!.
Qed.

Lemma proof_of_subst_term_return_wit_4 : subst_term_return_wit_4.
Proof. 
    pre_process.
    unfold term_subst_t.
    rewrite PreH2.
    unfold store_term.
    simpl.
    Exists retval retval_2.
    entailer!.
Qed.

Lemma proof_of_subst_term_return_wit_3 : subst_term_return_wit_3.
Proof.  
    pre_process.
    unfold term_subst_t.
    rewrite PreH2.
    unfold store_term.
    simpl.
    entailer!.
Qed.

Lemma proof_of_subst_term_return_wit_2 : subst_term_return_wit_2.
Proof. 
    pre_process.
    unfold list_Z_cmp in PreH2.
    destruct (list_Z_eqb var src_str) eqn:Heq; [ rewrite PreH2 in PreH1; contradiction | ].
    unfold term_subst_t.
    rewrite PreH4, Heq.
    unfold store_term.
    simpl.
    fold term_subst_t.
    fold store_term.
    Exists y.
    entailer!.
Qed.

Lemma proof_of_subst_term_return_wit_1 : subst_term_return_wit_1.
Proof. 
    pre_process.
    unfold list_Z_cmp in PreH3.
    rewrite PreH2 in PreH3.
    destruct (list_Z_eqb var src_str) eqn:Heq; [ | discriminate ].
    unfold term_subst_t.
    rewrite PreH5, Heq.
    unfold store_term.
    simpl.
    fold store_term.
    entailer!.
Qed.

Lemma proof_of_subst_term_partial_solve_wit_9_pure : subst_term_partial_solve_wit_9_pure.
Proof.
    pre_process.
    unfold store_string.
    Intros n.
    sep_apply (store_term_unfold y lt).
    entailer!.
Qed.

Lemma proof_of_subst_term_partial_solve_wit_10_pure : subst_term_partial_solve_wit_10_pure.
Proof. 
    pre_process.
    unfold store_string.
    Intros n.
    sep_apply (store_term_unfold z rt).
    entailer!.
Qed. 

Lemma proof_of_subst_term_partial_solve_wit_13_pure : subst_term_partial_solve_wit_13_pure.
Proof.
    pre_process.
    unfold store_string.
    Intros n1 n2.
    sep_apply (store_term_unfold z qterm).
    entailer!.
Qed. 

Lemma proof_of_subst_term_which_implies_wit_1 : subst_term_which_implies_wit_1.
Proof. 
    pre_process.
    sep_apply store_term_unfold.
    entailer!.
Qed.

Lemma proof_of_subst_term_which_implies_wit_2 : subst_term_which_implies_wit_2.
Proof. 
    pre_process.
    sep_apply store_term'_Var; [ | tauto | tauto].
    Intros var y.
    Exists y var.
    entailer!.
Qed. 

Lemma proof_of_subst_term_which_implies_wit_3 : subst_term_which_implies_wit_3.
Proof. 
    pre_process.
    rewrite PreH2.
    unfold store_term.
    Exists y.
    entailer!.
Qed.

Lemma proof_of_subst_term_which_implies_wit_4 : subst_term_which_implies_wit_4.
Proof.
    pre_process.
    sep_apply store_term'_Const; [ | tauto | tauto].
    Intros y z.
    Exists y z.
    entailer!.
Qed. 

Lemma proof_of_subst_term_which_implies_wit_5 : subst_term_which_implies_wit_5.
Proof. 
    pre_process.
    sep_apply store_term'_Apply; [ | tauto | tauto].
    Intros lt rt y z.
    Exists z y lt rt.
    entailer!.
Qed.

Lemma proof_of_subst_term_which_implies_wit_6 : subst_term_which_implies_wit_6.
Proof. 
    pre_process.
    sep_apply store_term'_Quant; [ | tauto | tauto].
    Intros typ v b y z.
    Exists z y typ v b.
    entailer!.
Qed.
