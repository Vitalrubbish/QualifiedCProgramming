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
From SimpleC.EE.QCP_demos_LLM Require Import swap_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
From SimpleC.EE.QCP_demos_LLM Require Import swap_lib.
Local Open Scope sac.

Lemma proof_of_swap_entail_wit_1 : swap_entail_wit_1.
Proof.
  pre_process.
  destruct para_all; simpl; entailer!.
  + Right.
    Exists z.
    entailer!.
  + Left.
    Exists z0 z.
    entailer!.
Qed.

Lemma proof_of_swap_return_wit_1 : swap_return_wit_1.
Proof.
  pre_process.
  subst.
  simpl.
  entailer!.
Qed.

Lemma proof_of_swap_return_wit_2 : swap_return_wit_2.
Proof.
  pre_process.
  subst.
  simpl.
  entailer!.
Qed.

Lemma proof_of_swap_derive_eq_by_all : swap_derive_eq_by_all.
Proof.
  pre_process.
  subst py_pre.
  Exists (swap_eq_para x_eq).
  simpl.
  entailer!.
  apply derivable1_wand_sepcon_adjoint.
  entailer!.
Qed.

Lemma proof_of_swap_derive_neq_by_all : swap_derive_neq_by_all.
Proof.
  pre_process.
  Exists (swap_neq_para x_neq y_neq).
  simpl.
  entailer!.
  apply derivable1_wand_sepcon_adjoint.
  entailer!.
Qed.
