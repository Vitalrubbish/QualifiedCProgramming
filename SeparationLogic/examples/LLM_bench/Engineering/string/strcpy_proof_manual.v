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
From SimpleC.EE.LLM_bench.Engineering.string Require Import strcpy_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.StdLib.string_lib.
Local Open Scope sac.

Lemma proof_of_strcpy_entail_wit_1 : strcpy_entail_wit_1.
Proof.
  pre_process.
  entailer!.
  - rewrite Zsublist_nil by lia.
    rewrite CharArray.full_empty.
    entailer!.
    apply CharArray.undef_full_to_undef_seg.
  - unfold string_lib.string_length; apply Zlength_nonneg.
Qed.

Lemma proof_of_strcpy_entail_wit_2 : strcpy_entail_wit_2.
Proof.
  pre_process.
  entailer!.
  - assert (Hi : i < string_lib.string_length src_str).
    {
      unfold string_lib.c_string, string_lib.string_length in *.
      destruct (Z_lt_ge_dec i (Zlength src_str)) as [Hlt | Hge]; [lia |].
      assert (i = Zlength src_str) as -> by lia.
      rewrite app_Znth2 in PreH2 by lia.
      replace (Zlength src_str - Zlength src_str) with 0 in PreH2 by lia.
      rewrite Znth0_cons in PreH2.
      contradiction.
    }
    replace (sublist 0 (i + 1) src_str)
      with (sublist 0 i src_str ++
            Znth i (string_lib.c_string src_str) 0 :: nil).
    2: {
      rewrite (sublist_split 0 (i + 1) i src_str).
      - rewrite (sublist_single 0 i src_str).
        + unfold string_lib.c_string.
          rewrite app_Znth1; [reflexivity |].
          unfold string_lib.string_length in Hi; lia.
        + unfold string_lib.string_length in Hi; lia.
      - lia.
      - unfold string_lib.string_length in Hi; lia.
    }
    unfold string_lib.store_string.
    entailer!.
  - assert (Hi : i < string_lib.string_length src_str).
    {
      unfold string_lib.c_string, string_lib.string_length in *.
      destruct (Z_lt_ge_dec i (Zlength src_str)) as [Hlt | Hge]; [lia |].
      assert (i = Zlength src_str) as -> by lia.
      rewrite app_Znth2 in PreH2 by lia.
      replace (Zlength src_str - Zlength src_str) with 0 in PreH2 by lia.
      rewrite Znth0_cons in PreH2.
      contradiction.
    }
    lia.
Qed.

Lemma proof_of_strcpy_return_wit_1 : strcpy_return_wit_1.
Proof.
  pre_process.
  assert (Hi : i = string_lib.string_length src_str).
  {
    unfold string_lib.valid_string in PreH3.
    destruct PreH3 as [_ Hno].
    unfold string_lib.c_string, string_lib.string_length in *.
    destruct (Z_lt_ge_dec i (Zlength src_str)) as [Hlt | Hge].
    - rewrite app_Znth1 in PreH2 by lia.
      exfalso.
      apply (Hno i); [lia | assumption].
    - lia.
  }
  subst i.
  unfold string_lib.store_string, string_lib.c_string, string_lib.string_length in *.
  rewrite sublist_self by reflexivity.
  entailer!.
  rewrite CharArray.undef_seg_empty.
  entailer!.
Qed.

Lemma proof_of_strncpy_entail_wit_1 : strncpy_entail_wit_1.
Proof.
  pre_process.
  split_pure_spatial.
  - rewrite (Zsublist_nil src_str 0 0) by lia.
    sep_apply (CharArray.undef_full_split_to_undef_seg dest_pre 0 n_pre).
    + sep_apply (strncpy_undef_seg_empty_to_full_nil dest_pre).
      entailer!.
    + lia.
  - entailer!.
    unfold string_lib.string_length.
    apply Zlength_nonneg.
Qed.

Lemma proof_of_strncpy_entail_wit_2 : strncpy_entail_wit_2.
Proof.
  pre_process.
  split_pure_spatial.
  - rewrite (strncpy_sublist_succ src_str i PreH2 PreH7 PreH9).
    unfold string_lib.store_string.
    entailer!.
  - entailer!.
    pose proof (strncpy_c_string_nonzero_lt src_str i PreH2 PreH7 PreH9).
    lia.
Qed.

Lemma proof_of_strncpy_entail_wit_3_1 : strncpy_entail_wit_3_1.
Proof.
  pre_process.
  Exists (sublist 0 i src_str).
  split_pure_spatial.
  - unfold string_lib.store_string.
    entailer!.
  - entailer!.
    unfold strncpy_content.
    split; [lia |].
    left; split; [lia | reflexivity].
Qed.

Lemma proof_of_strncpy_entail_wit_3_2 : strncpy_entail_wit_3_2.
Proof.
  pre_process.
  Exists (sublist 0 i src_str).
  split_pure_spatial.
  - cancel (CharArray.full dest_pre i (sublist 0 i src_str)).
    cancel (CharArray.undef_seg dest_pre i n_pre).
    cancel (string_lib.store_string src_pre src_str).
  - split_pures; dump_pre_spatial; try lia; auto.
    unfold strncpy_content.
    split; [lia|].
    left.
    split; [lia | reflexivity].
    intros _.
    eapply strncpy_c_string_zero_ge_length; eauto.
Qed. 

Lemma proof_of_strncpy_entail_wit_4 : strncpy_entail_wit_4.
Proof.
  pre_process.
  Exists (out_2 ++ 0 :: nil).
  split_pure_spatial.
  - unfold string_lib.store_string.
    cancel (CharArray.full dest_pre (i + 1) (out_2 ++ 0 :: nil)).
    cancel (CharArray.undef_seg dest_pre (i + 1) n_pre).
    cancel (CharArray.full src_pre (string_lib.string_length src_str + 1)
              (string_lib.c_string src_str)).
  - split_pures; dump_pre_spatial; try lia; auto.
    apply strncpy_content_pad_zero_step; auto.
Qed. 

Lemma proof_of_strncpy_return_wit_1 : strncpy_return_wit_1.
Proof.
  pre_process.
  assert (i = n_pre) by lia.
  subst i.
  Exists out_2.
  split_pure_spatial.
  - cancel (CharArray.full dest_pre n_pre out_2).
    cancel (string_lib.store_string src_pre src_str).
    apply (proj1 (CharArray.undef_seg_empty dest_pre n_pre)).
  - split_pures; dump_pre_spatial; auto.
Qed. 
