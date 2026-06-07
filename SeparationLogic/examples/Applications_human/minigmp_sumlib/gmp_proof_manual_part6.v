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
From SimpleC.SL Require Import Mem SeparationLogic IntLib.
From SimpleC.EE.Applications_human.minigmp_sumlib Require Import gmp_goal GmpMulAux.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
From SimpleC.EE.Applications_human.minigmp_sumlib Require Import GmpAux GmpNumber GmpMulAux.
Import Aux.
Local Open Scope sac.


Lemma proof_of_gmp_umul_ppmm_return_wit_1 : gmp_umul_ppmm_return_wit_1.
Proof.
  pre_process.
  
  Exists (unsigned_last_nbits (((unsigned_last_nbits ((Z.shiftl (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((Z.land u_pre 65535) * (Z.shiftr v_pre 16) )) (32)) + (Z.shiftr (unsigned_last_nbits (((Z.land u_pre 65535) * (Z.land v_pre 65535) )) (32)) 16) )) (32)) + (unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.land v_pre 65535) )) (32)) )) (32)) 16)) (32)) + (Z.land ((Z.land u_pre 65535) * (Z.land v_pre 65535) ) 65535) )) (32)).
  Exists (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.shiftr v_pre 16) )) (32)) + 65536 )) (32)) + (Z.shiftr (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((Z.land u_pre 65535) * (Z.shiftr v_pre 16) )) (32)) + (Z.shiftr (unsigned_last_nbits (((Z.land u_pre 65535) * (Z.land v_pre 65535) )) (32)) 16) )) (32)) + (unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.land v_pre 65535) )) (32)) )) (32)) 16) )) (32)).
  
  entailer!.
  
  unfold UINT_MOD.
  
  set (ul := Z.land u_pre 65535).
  set (uh := Z.shiftr u_pre 16).
  set (vl := Z.land v_pre 65535).
  set (vh := Z.shiftr v_pre 16).
  set (x0 := ul * vl).
  set (x1 := ul * vh).
  set (x2 := uh * vl).
  set (x3 := uh * vh).
  set (x1' := (x1 + Z.shiftr x0 16) mod 4294967296).
  set (x1'' := (x1' + x2) mod 4294967296).
  
  set (w1 := ((x3 + 65536) mod 4294967296 + Z.shiftr x1'' 16) mod 4294967296).
  set (w0 := ((Z.shiftl x1'' 16) mod 4294967296 + Z.land x0 65535) mod 4294967296).
  assert (Hu32: 0 <= u_pre < 4294967296) by lia.
  assert (Hv32: 0 <= v_pre < 4294967296) by lia.
  
  pose proof (umul_ppmm_correct_with_carry u_pre v_pre ul uh vl vh x0 x1 x2 x3
    Hu32
    Hv32
    eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl) as Hlemma.
  
  assert (Hcarry: x1'' < x2). {
    assert (Hx1pp_bounds: 0 <= x1'' < 4294967296).
    { unfold x1'', x1'. apply Z.mod_pos_bound. lia. }
    assert (Hx2_bounds: 0 <= x2 < 4294967296).
    { unfold x2, uh, vl.
      pose proof (shiftr_16_full_bounds u_pre Hu32) as Huh.
      pose proof (land_65535_bounds_alt v_pre) as Hvl.
      split.
      + apply Z.mul_nonneg_nonneg; lia.
      + assert (Z.shiftr u_pre 16 * Z.land v_pre 65535 < 65536 * 65536) by nia.
        lia. }
    assert (Hcarry_bits: unsigned_last_nbits x1'' 32 < unsigned_last_nbits x2 32).
    { unfold x1'', x1', x0, x1, x2, ul, uh, vl, vh.
      apply (carry_condition_transform u_pre v_pre); [exact Hu32 | exact Hv32 | exact PreH1].
    }
    rewrite (unsigned_last_nbits_eq x1'' 32) in Hcarry_bits by lia.
    rewrite (unsigned_last_nbits_eq x2 32) in Hcarry_bits by lia.
    exact Hcarry_bits.
  }
  
  specialize (Hlemma Hcarry).
  
  unfold w1, w0 in Hlemma.
  unfold x1'', x1', x3, x2, x1, x0, vh, vl, uh, ul in Hlemma.
  
  repeat (unfold unsigned_last_nbits; change (2 ^ 32) with 4294967296).
  
  unfold x1'', x1', x3, x2, x1, x0, vh, vl, uh, ul.
  
  pose proof Hu32 as Hu.
  pose proof Hv32 as Hv.
  
  
  assert (Hul_bounds: 0 <= Z.land u_pre 65535 < 65536) by (apply land_65535_bounds_alt).
  assert (Hvl_bounds: 0 <= Z.land v_pre 65535 < 65536) by (apply land_65535_bounds_alt).
  assert (Huh_bounds: 0 <= Z.shiftr u_pre 16 < 65536) by (apply shiftr_16_full_bounds; exact Hu).
  assert (Hvh_bounds: 0 <= Z.shiftr v_pre 16 < 65536) by (apply shiftr_16_full_bounds; exact Hv).
  
  assert (Hx0_small: 0 <= Z.land u_pre 65535 * Z.land v_pre 65535 < 4294967296) by nia.
  assert (Hx1_small: 0 <= Z.land u_pre 65535 * Z.shiftr v_pre 16 < 4294967296) by nia.
  assert (Hx2_small: 0 <= Z.shiftr u_pre 16 * Z.land v_pre 65535 < 4294967296) by nia.
  assert (Hx3_small: 0 <= Z.shiftr u_pre 16 * Z.shiftr v_pre 16 < 4294967296) by nia.
  
  rewrite (Z.mod_small (Z.land u_pre 65535 * Z.land v_pre 65535) 4294967296) by lia.
  rewrite (Z.mod_small (Z.land u_pre 65535 * Z.shiftr v_pre 16) 4294967296) by lia.
  rewrite (Z.mod_small (Z.shiftr u_pre 16 * Z.land v_pre 65535) 4294967296) by lia.
  rewrite (Z.mod_small (Z.shiftr u_pre 16 * Z.shiftr v_pre 16) 4294967296) by lia.
  
  exact Hlemma.
Qed.


Lemma proof_of_gmp_umul_ppmm_return_wit_2 : gmp_umul_ppmm_return_wit_2.
Proof.
  pre_process.
  Exists (unsigned_last_nbits (((unsigned_last_nbits ((Z.shiftl (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((Z.land u_pre 65535) * (Z.shiftr v_pre 16) )) (32)) + (Z.shiftr (unsigned_last_nbits (((Z.land u_pre 65535) * (Z.land v_pre 65535) )) (32)) 16) )) (32)) + (unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.land v_pre 65535) )) (32)) )) (32)) 16)) (32)) + (Z.land ((Z.land u_pre 65535) * (Z.land v_pre 65535) ) 65535) )) (32)).
  Exists (unsigned_last_nbits (((unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.shiftr v_pre 16) )) (32)) + (Z.shiftr (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((Z.land u_pre 65535) * (Z.shiftr v_pre 16) )) (32)) + (Z.shiftr (unsigned_last_nbits (((Z.land u_pre 65535) * (Z.land v_pre 65535) )) (32)) 16) )) (32)) + (unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.land v_pre 65535) )) (32)) )) (32)) 16) )) (32)).
  
  entailer!.
  
  unfold UINT_MOD.
  
  set (ul := Z.land u_pre 65535).
  set (uh := Z.shiftr u_pre 16).
  set (vl := Z.land v_pre 65535).
  set (vh := Z.shiftr v_pre 16).
  set (x0 := ul * vl).
  set (x1 := ul * vh).
  set (x2 := uh * vl).
  set (x3 := uh * vh).
  set (x1' := (x1 + Z.shiftr x0 16) mod 4294967296).
  set (x1'' := (x1' + x2) mod 4294967296).
  
  set (w1 := (x3 + Z.shiftr x1'' 16) mod 4294967296).
  set (w0 := ((Z.shiftl x1'' 16) mod 4294967296 + Z.land x0 65535) mod 4294967296).
  assert (Hu32: 0 <= u_pre < 4294967296) by lia.
  assert (Hv32: 0 <= v_pre < 4294967296) by lia.
  
  pose proof (umul_ppmm_correct_no_carry u_pre v_pre ul uh vl vh x0 x1 x2 x3
    Hu32
    Hv32
    eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl) as Hlemma.
  
  assert (Hnocarry: x1'' >= x2). {
    pose proof Hu32 as Hu.
    pose proof Hv32 as Hv.
    

    assert (Hx1_exp: 0 <= Z.land u_pre 65535 * Z.shiftr v_pre 16 < 4294967296).
    { pose proof (land_65535_bounds_alt u_pre) as Hul.
      pose proof (shiftr_16_full_bounds v_pre Hv) as Hvh.
      split; [apply Z.mul_nonneg_nonneg; lia | nia]. }
    assert (Hx0_exp: 0 <= Z.land u_pre 65535 * Z.land v_pre 65535 < 4294967296).
    { pose proof (land_65535_bounds_alt u_pre) as Hul.
      pose proof (land_65535_bounds_alt v_pre) as Hvl.
      split; [apply Z.mul_nonneg_nonneg; lia | nia]. }
    assert (Hx2_exp: 0 <= Z.shiftr u_pre 16 * Z.land v_pre 65535 < 4294967296).
    { pose proof (shiftr_16_full_bounds u_pre Hu) as Huh.
      pose proof (land_65535_bounds_alt v_pre) as Hvl.
      split; [apply Z.mul_nonneg_nonneg; lia | nia]. }

    rewrite (unsigned_last_nbits_eq (Z.land u_pre 65535 * Z.shiftr v_pre 16) 32) in PreH1 by lia.
    rewrite (unsigned_last_nbits_eq (Z.land u_pre 65535 * Z.land v_pre 65535) 32) in PreH1 by lia.
    rewrite (unsigned_last_nbits_eq (Z.shiftr u_pre 16 * Z.land v_pre 65535) 32) in PreH1 by lia.
    unfold unsigned_last_nbits in PreH1.
    change (2 ^ 32) with 4294967296 in PreH1.
    unfold x1'', x1', x0, x1, x2, ul, uh, vl, vh.
    exact PreH1.
  }
  
  specialize (Hlemma Hnocarry).
  
  unfold w1, w0 in Hlemma.
  unfold x1'', x1', x3, x2, x1, x0, vh, vl, uh, ul in Hlemma.
  
  repeat (unfold unsigned_last_nbits; change (2 ^ 32) with 4294967296).
  
  unfold x1'', x1', x3, x2, x1, x0, vh, vl, uh, ul.
  
  pose proof Hu32 as Hu.
  pose proof Hv32 as Hv.
  
  
  assert (Hul_bounds: 0 <= Z.land u_pre 65535 < 65536) by (apply land_65535_bounds_alt).
  assert (Hvl_bounds: 0 <= Z.land v_pre 65535 < 65536) by (apply land_65535_bounds_alt).
  assert (Huh_bounds: 0 <= Z.shiftr u_pre 16 < 65536) by (apply shiftr_16_full_bounds; exact Hu).
  assert (Hvh_bounds: 0 <= Z.shiftr v_pre 16 < 65536) by (apply shiftr_16_full_bounds; exact Hv).
  
  assert (Hx0_small: 0 <= Z.land u_pre 65535 * Z.land v_pre 65535 < 4294967296) by nia.
  assert (Hx1_small: 0 <= Z.land u_pre 65535 * Z.shiftr v_pre 16 < 4294967296) by nia.
  assert (Hx2_small: 0 <= Z.shiftr u_pre 16 * Z.land v_pre 65535 < 4294967296) by nia.
  assert (Hx3_small: 0 <= Z.shiftr u_pre 16 * Z.shiftr v_pre 16 < 4294967296) by nia.
  
  rewrite (Z.mod_small (Z.land u_pre 65535 * Z.land v_pre 65535) 4294967296) by lia.
  rewrite (Z.mod_small (Z.land u_pre 65535 * Z.shiftr v_pre 16) 4294967296) by lia.
  rewrite (Z.mod_small (Z.shiftr u_pre 16 * Z.land v_pre 65535) 4294967296) by lia.
  rewrite (Z.mod_small (Z.shiftr u_pre 16 * Z.shiftr v_pre 16) 4294967296) by lia.
  
  exact Hlemma.
Qed.


Lemma proof_of_mpn_mul_1_entail_wit_1 : mpn_mul_1_entail_wit_1.
Proof.
  pre_process.
  Exists (@nil Z).
  entailer!.
  sep_apply UIntArray.undef_full_to_undef_seg.
  entailer!.
  rewrite (UIntArray.seg_empty rp_pre 0 0).
  entailer!.
Qed. 


Lemma proof_of_mpn_mul_1_entail_wit_5_1 : mpn_mul_1_entail_wit_5_1.
Proof.
  pre_process.
  Exists (l_rp_2 ++ (unsigned_last_nbits (lpl + cl) 32 :: nil)).
  entailer!.
  - sep_apply (store_uint_undef_store_uint &("lpl")).
    sep_apply (store_uint_undef_store_uint &("hpl")).
    sep_apply (store_uint_undef_store_uint &("ul")).
    entailer!.
  - 
    simpl. apply mpn_mul_1_no_carry_invariant with (vl_pre := vl_pre); try lia; auto.
    + unfold UINT_MOD. lia.
    + assert (Hw0: 0 <= lpl < UINT_MOD) by (unfold UINT_MOD in *; lia). unfold UINT_MOD in *. lia.
    + assert (Hw1: 0 <= hpl < UINT_MOD) by (unfold UINT_MOD in *; lia). unfold UINT_MOD in *. lia.
    + unfold UINT_MOD. lia.
  - apply list_within_bound_concat; auto. simpl. split; auto.
    unfold unsigned_last_nbits, UINT_MOD. pose proof (Z.mod_pos_bound (lpl + cl) (2^32)). lia.
  - rewrite Zlength_app. rewrite Zlength_cons. rewrite Zlength_nil. lia.
Qed. 


Lemma proof_of_mpn_mul_1_entail_wit_5_2 : mpn_mul_1_entail_wit_5_2.
Proof.
  pre_process.
  Exists (l_rp_2 ++ (unsigned_last_nbits (lpl + cl) 32 :: nil)).
  entailer!.
  -
    sep_apply (store_uint_undef_store_uint &("lpl")).
    sep_apply (store_uint_undef_store_uint &("hpl")).
    sep_apply (store_uint_undef_store_uint &("ul")).
    entailer!.
  -
    simpl. apply mpn_mul_1_carry_invariant with (vl_pre := vl_pre); try lia; auto.
    + unfold UINT_MOD. lia.
    + assert (Hw0: 0 <= lpl < UINT_MOD) by (unfold UINT_MOD in *; lia). exact Hw0.
    + assert (Hw1: 0 <= hpl < UINT_MOD) by (unfold UINT_MOD in *; lia). exact Hw1.
    + unfold UINT_MOD. lia.
  - 
    apply list_within_bound_concat; auto. simpl. split; auto.
    unfold unsigned_last_nbits, UINT_MOD. pose proof (Z.mod_pos_bound (lpl + cl) (2^32)). lia.
  - 
    rewrite Zlength_app. rewrite Zlength_cons. rewrite Zlength_nil. lia.
  - unfold unsigned_last_nbits, UINT_MOD.
    pose proof (Z.mod_pos_bound (1 + hpl) (2^32)).
    lia.
  - unfold unsigned_last_nbits, UINT_MOD.
    pose proof (Z.mod_pos_bound (1 + hpl) (2^32)).
    lia.
Qed.


Lemma proof_of_mpn_mul_1_return_wit_1 : mpn_mul_1_return_wit_1.
Proof.
  pre_process.
  Exists (list_to_Z UINT_MOD l_rp) l_rp.
  entailer!.
  - assert (Hi_eq: i = n_pre) by lia. rewrite Hi_eq.
    rewrite (UIntArray.undef_seg_empty rp_pre n_pre).
    unfold UIntArray.full, UIntArray.seg. entailer!.
  - assert (Hi_eq: i = n_pre) by lia. rewrite Hi_eq in *.
    rewrite (sublist_self l n_pre) in PreH8 by lia. lia.
Qed. 

