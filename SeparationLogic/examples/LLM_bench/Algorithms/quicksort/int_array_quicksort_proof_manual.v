Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.micromega.Lia.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
From SimpleC.EE.LLM_bench.Algorithms.quicksort Require Import int_array_quicksort_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Algorithms.quicksort.int_array_quicksort_lib.
Local Open Scope sac.

Lemma same_outside_range_refl :
  forall (l: list Z) left right,
    same_outside_range l l left right.
Proof.
  intros l left right.
  unfold same_outside_range.
  split.
  - reflexivity.
  - intros k Hk _.
    reflexivity.
Qed.

Lemma same_outside_range_trans :
  forall (l l1 l2: list Z) left right,
    same_outside_range l l1 left right ->
    same_outside_range l1 l2 left right ->
    same_outside_range l l2 left right.
Proof.
  intros l l1 l2 left right [Hlen1 Heq1] [Hlen2 Heq2].
  unfold same_outside_range.
  split.
  - rewrite Hlen1. exact Hlen2.
  - intros k Hk Hout.
    assert (Hk1 : 0 <= k < Zlength l1) by (rewrite <- Hlen1; exact Hk).
    rewrite (Heq2 k Hk1 Hout).
    apply Heq1; assumption.
Qed.

Lemma same_outside_range_weaken :
  forall (l l1: list Z) left1 right1 left2 right2,
    left2 <= left1 ->
    right1 <= right2 ->
    same_outside_range l l1 left1 right1 ->
    same_outside_range l l1 left2 right2.
Proof.
  intros l l1 left1 right1 left2 right2 Hleft Hright [Hlen Heq].
  unfold same_outside_range.
  split.
  - exact Hlen.
  - intros k Hk Hout.
    apply Heq; try assumption.
    destruct Hout as [Hout | Hout].
    + left; lia.
    + right; lia.
Qed.

Lemma Forall_permutation :
  forall (P: Z -> Prop) l1 l2,
    permutation l1 l2 ->
    Forall P l1 ->
    Forall P l2.
Proof.
  intros P l1 l2 Hperm.
  induction Hperm; intros HForall.
  - exact HForall.
  - inversion HForall; subst.
    constructor; auto.
  - repeat match goal with
      | H : Forall _ (_ :: _) |- _ => inversion H; subst; clear H
    end.
    constructor; auto.
  - apply IHHperm2.
    apply IHHperm1.
    exact HForall.
Qed.

Lemma Forall_Znth :
  forall (P: Z -> Prop) (l: list Z) i (d: Z),
    Forall P l ->
    0 <= i < Zlength l ->
    P (Znth i l d).
Proof.
  intros P l i d HForall Hrange.
  apply Forall_forall with (x := Znth i l d) in HForall.
  - exact HForall.
  - unfold Znth.
    apply nth_In.
    rewrite Zlength_correct in Hrange.
    lia.
Qed.

Lemma Znth_replace_eq :
  forall (l: list Z) n (a d: Z),
    0 <= n < Zlength l ->
    Znth n (replace_Znth n a l) d = a.
Proof.
  intros l n a d Hn.
  unfold Znth, replace_Znth.
  rewrite Zlength_correct in Hn.
  remember (Z.to_nat n) as m eqn:Hm.
  assert (HmLen : (m < length l)%nat) by lia.
  clear Hn Hm n.
  revert l HmLen.
  induction m; intros l HmLen.
  - destruct l; simpl in *.
    + lia.
    + reflexivity.
  - destruct l; simpl in *.
    + lia.
    + apply IHm. lia.
Qed.

Lemma Znth_replace_neq :
  forall (l: list Z) i j (a d: Z),
    0 <= i < Zlength l ->
    0 <= j ->
    i <> j ->
    Znth i (replace_Znth j a l) d = Znth i l d.
Proof.
  intros l i j a d Hi Hj Hneq.
  unfold Znth, replace_Znth.
  rewrite Zlength_correct in Hi.
  remember (Z.to_nat i) as ni eqn:HiNat.
  remember (Z.to_nat j) as nj eqn:HjNat.
  assert (HiEq : i = Z.of_nat ni) by (subst; symmetry; apply Z2Nat.id; lia).
  assert (HjEq : j = Z.of_nat nj) by (subst; symmetry; apply Z2Nat.id; lia).
  assert (HiLen : (ni < length l)%nat) by lia.
  assert (HneqNat : ni <> nj).
  {
    intro Heq.
    apply Hneq.
    rewrite HiEq, HjEq.
    now rewrite Heq.
  }
  clear Hi Hj Hneq HiNat HjNat HiEq HjEq i j.
  revert nj l HiLen HneqNat.
  induction ni; intros nj l HiLen HneqNat.
  - destruct l; simpl in *; try lia.
    destruct nj; [contradiction HneqNat; reflexivity | reflexivity].
  - destruct l; simpl in *; try lia.
    destruct nj; simpl.
    + reflexivity.
    + apply IHni.
      * lia.
      * intro Heq.
        apply HneqNat.
        now f_equal.
Qed.

Lemma sublist_eq_from_Znth :
  forall (l1 l2: list Z) lo hi,
    Zlength l1 = Zlength l2 ->
    0 <= lo <= hi ->
    hi <= Zlength l1 ->
    (forall k, lo <= k < hi -> Znth k l1 0 = Znth k l2 0) ->
    sublist lo hi l1 = sublist lo hi l2.
Proof.
  intros l1 l2 lo hi Hlen Hlohi Hhilen Hpoint.
  apply (proj2 (list_eq_ext (sublist lo hi l1) (sublist lo hi l2) 0)).
  split.
  - repeat rewrite Zlength_correct.
    repeat rewrite sublist_length by
      (try exact Hlohi; try rewrite <- Hlen; exact Hhilen).
    lia.
  - intros i Hi.
    assert (Hi' : 0 <= i < hi - lo).
    {
      rewrite Zlength_sublist in Hi by lia.
      exact Hi.
    }
    rewrite (@Znth_sublist_lt Z 0 lo hi l1 i).
    2: exact Hlohi.
    2: { exact Hhilen. }
    2: exact Hi'.
    rewrite (@Znth_sublist_lt Z 0 lo hi l2 i).
    2: exact Hlohi.
    2: { rewrite <- Hlen. exact Hhilen. }
    2: exact Hi'.
    apply Hpoint.
    lia.
Qed.

Lemma list_decompose_sublist :
  forall (l: list Z) lo hi,
    0 <= lo <= hi ->
    hi <= Zlength l ->
    l = sublist 0 lo l ++ sublist lo hi l ++ sublist hi (Zlength l) l.
Proof.
  intros l lo hi Hlohi Hhilen.
  rewrite <- (sublist_self l (Zlength l)) at 1 by reflexivity.
  rewrite (sublist_split 0 (Zlength l) lo l).
  2: lia.
  2: {
    split.
    - transitivity hi; lia.
    - lia.
  }
  rewrite (sublist_split lo (Zlength l) hi l).
  2: lia.
  2: {
    split.
    - exact Hhilen.
    - lia.
  }
  reflexivity.
Qed.

Lemma same_outside_range_prefix :
  forall (l l1: list Z) left right,
    same_outside_range l l1 left right ->
    0 <= left <= Zlength l ->
    sublist 0 left l1 = sublist 0 left l.
Proof.
  intros l l1 left right Hsame Hrange.
  destruct Hsame as [Hlen Heq].
  apply sublist_eq_from_Znth.
  - symmetry. exact Hlen.
  - lia.
  - lia.
  - intros k Hk.
    apply Heq.
    + lia.
    + left. lia.
Qed.

Lemma same_outside_range_suffix :
  forall (l l1: list Z) left right,
    same_outside_range l l1 left right ->
    0 <= right + 1 <= Zlength l ->
    sublist (right + 1) (Zlength l1) l1 = sublist (right + 1) (Zlength l) l.
Proof.
  intros l l1 left right Hsame Hrange.
  destruct Hsame as [Hlen Heq].
  rewrite <- Hlen.
  apply sublist_eq_from_Znth.
  - symmetry. exact Hlen.
  - lia.
  - lia.
  - intros k Hk.
    apply Heq.
    + rewrite Hlen. lia.
    + right. lia.
Qed.

Lemma middle_permutation_of_same_outside :
  forall (l l1: list Z) left right,
    permutation l l1 ->
    same_outside_range l l1 left right ->
    0 <= left <= right + 1 ->
    right + 1 <= Zlength l ->
    permutation (sublist left (right + 1) l) (sublist left (right + 1) l1).
Proof.
  intros l l1 left right Hperm Hsame Hlr Hlenr.
  pose proof Hsame as Hsame0.
  destruct Hsame as [Hlen _].
  pose proof (same_outside_range_prefix _ _ _ _ Hsame0) as Hpre.
  pose proof (same_outside_range_suffix _ _ _ _ Hsame0) as Hsuf.
  rewrite (list_decompose_sublist l left (right + 1)) in Hperm by lia.
  assert (Hlenr1 : right + 1 <= Zlength l1) by (rewrite <- Hlen; exact Hlenr).
  rewrite (list_decompose_sublist l1 left (right + 1)) in Hperm by lia.
  specialize (Hpre ltac:(lia)).
  specialize (Hsuf ltac:(lia)).
  rewrite Hpre, Hsuf in Hperm.
  apply Permutation_app_inv_l in Hperm.
  apply Permutation_app_inv_r in Hperm.
  exact Hperm.
Qed.

Lemma Forall_sublist_by_Znth :
  forall (P: Z -> Prop) (l: list Z) lo hi,
    0 <= lo <= hi ->
    hi <= Zlength l ->
    (forall k, lo <= k < hi -> P (Znth k l 0)) ->
    Forall P (sublist lo hi l).
Proof.
  intros P l lo hi Hlohi Hhilen Hpoint.
  remember (Z.to_nat (hi - lo)) as n eqn:Hn.
  revert lo hi Hlohi Hhilen Hpoint Hn.
  induction n; intros lo hi Hlohi Hhilen Hpoint Hn.
  - assert (hi = lo) by lia.
    subst hi.
    rewrite Zsublist_nil by lia.
    constructor.
  - assert (lo < hi) by lia.
    rewrite (sublist_split lo hi (lo + 1) l).
    2: lia.
	    2: {
	      split.
	      - lia.
	      - exact Hhilen.
	    }
	    rewrite (@sublist_single Z 0 lo l) by lia.
    constructor.
    + simpl. apply Hpoint. lia.
    + apply IHn with (lo := lo + 1) (hi := hi).
      * lia.
      * exact Hhilen.
      * intros k Hk. apply Hpoint. lia.
      * assert (Hn' : Z.to_nat (hi - (lo + 1)) = n) by lia.
        symmetry. exact Hn'.
Qed.

Lemma same_outside_range_swap_inside :
  forall (l: list Z) low high i j,
    0 <= low ->
    low <= i <= high ->
    low <= j <= high ->
    high < Zlength l ->
    same_outside_range l
      (replace_Znth j (Znth i l 0) (replace_Znth i (Znth j l 0) l))
      low high.
Proof.
  intros l low high i j Hlow Hi Hj Hhigh.
  unfold same_outside_range.
  split.
  - rewrite !Zlength_replace_Znth. reflexivity.
  - intros k Hk Hout.
    assert (Hkj : k <> j).
    { intro Heq. subst k. destruct Hout as [Hout | Hout]; lia. }
    assert (Hki : k <> i).
    { intro Heq. subst k. destruct Hout as [Hout | Hout]; lia. }
    rewrite (Znth_replace_neq (replace_Znth i (Znth j l 0) l) k j (Znth i l 0) 0).
    2: { rewrite Zlength_replace_Znth. exact Hk. }
    2: lia.
    2: exact Hkj.
    rewrite (Znth_replace_neq l k i (Znth j l 0) 0).
    2: exact Hk.
    2: lia.
    2: exact Hki.
    reflexivity.
Qed.

Lemma partitioned_at_preserved_by_left :
  forall l l1 left right p,
    permutation l l1 ->
    0 <= left ->
    same_outside_range l l1 left (p - 1) ->
    right < Zlength l ->
    partitioned_at l left right p ->
    partitioned_at l1 left right p.
Proof.
  intros l l1 left right p Hperm Hleft0 Hsame Hlen Hpart.
  destruct Hsame as [Hlen' Heq].
  destruct Hpart as [Hrange [Hleft Hright]].
  assert (Hpiv: Znth p l1 0 = Znth p l 0).
  {
    assert (Hp : 0 <= p < Zlength l) by lia.
    apply Heq.
    - exact Hp.
    - right. lia.
  }
  split.
  - lia.
  - split.
    + rewrite Hpiv.
      eapply (Forall_permutation
                (fun x => x <= Znth p l 0)
                (sublist left p l)
                (sublist left p l1)).
      * assert (Hmid :
            permutation (sublist left (p - 1 + 1) l)
                        (sublist left (p - 1 + 1) l1)).
        {
          eapply middle_permutation_of_same_outside
            with (left := left) (right := p - 1).
          - exact Hperm.
          - exact (conj Hlen' Heq).
          - lia.
          - lia.
        }
        replace (p - 1 + 1) with p in Hmid by lia.
        exact Hmid.
      * exact Hleft.
    + rewrite Hpiv.
      apply Forall_sublist_by_Znth; try lia.
      intros k Hk.
      rewrite Heq by (try lia; right; lia).
      assert (Hk' : 0 <= k - (p + 1) < Zlength (sublist (p + 1) (right + 1) l)) by
        (rewrite Zlength_sublist by lia; lia).
      pose proof (Forall_Znth _ _ (k - (p + 1)) 0 Hright Hk') as Hz.
      rewrite (@Znth_sublist_lt Z 0 (p + 1) (right + 1) l (k - (p + 1))) in Hz.
      2: lia.
	      2: { lia. }
      2: {
        rewrite Zlength_sublist in Hk' by lia.
        exact Hk'.
      }
      replace (p + 1 + (k - (p + 1))) with k in Hz by lia.
      exact Hz.
Qed.

Lemma partitioned_at_preserved_by_right :
  forall l l1 left right p,
    permutation l l1 ->
    0 <= left ->
    same_outside_range l l1 (p + 1) right ->
    right < Zlength l ->
    partitioned_at l left right p ->
    partitioned_at l1 left right p.
Proof.
  intros l l1 left right p Hperm Hleft0 Hsame Hlen Hpart.
  destruct Hsame as [Hlen' Heq].
  destruct Hpart as [Hrange [Hleft Hright]].
  assert (Hpiv: Znth p l1 0 = Znth p l 0).
  {
    assert (Hp : 0 <= p < Zlength l) by lia.
    apply Heq.
    - exact Hp.
    - left. lia.
  }
  split.
  - lia.
  - split.
    + rewrite Hpiv.
      assert (Hsub : sublist left p l1 = sublist left p l).
      {
        apply sublist_eq_from_Znth.
        - symmetry. exact Hlen'.
        - lia.
        - lia.
        - intros k Hk.
          apply Heq.
          * lia.
          * left. lia.
      }
      rewrite Hsub.
      exact Hleft.
    + rewrite Hpiv.
      eapply (Forall_permutation
                (fun x => Znth p l 0 < x)
                (sublist (p + 1) (right + 1) l)
                (sublist (p + 1) (right + 1) l1)).
      * assert (Hmid :
            permutation (sublist (p + 1) (right + 1) l)
                        (sublist (p + 1) (right + 1) l1)).
        {
          eapply middle_permutation_of_same_outside
            with (left := p + 1) (right := right).
          - exact Hperm.
          - exact (conj Hlen' Heq).
          - lia.
          - lia.
        }
        exact Hmid.
      * exact Hright.
Qed.

Lemma partitioned_at_ext :
  forall l l1 left right p,
    0 <= left ->
    right < Zlength l ->
    Zlength l = Zlength l1 ->
    (forall k, left <= k <= right -> Znth k l1 0 = Znth k l 0) ->
    partitioned_at l left right p ->
    partitioned_at l1 left right p.
Proof.
  intros l l1 left right p Hleft0 Hrightlen Hlen Heq [Hrange [Hleft Hright]].
  assert (Hpiv : Znth p l1 0 = Znth p l 0).
  { apply Heq. lia. }
  split.
  - lia.
  - split.
    + assert (Hsub : sublist left p l1 = sublist left p l).
      {
        apply sublist_eq_from_Znth.
        - symmetry. exact Hlen.
        - lia.
        - rewrite <- Hlen. lia.
        - intros k Hk. apply Heq. lia.
      }
      rewrite Hpiv.
      rewrite Hsub.
      exact Hleft.
    + assert (Hsub : sublist (p + 1) (right + 1) l1 = sublist (p + 1) (right + 1) l).
      {
        apply sublist_eq_from_Znth.
        - symmetry. exact Hlen.
        - lia.
        - rewrite <- Hlen. lia.
        - intros k Hk. apply Heq. lia.
      }
      rewrite Hpiv.
      rewrite Hsub.
      exact Hright.
Qed.

Lemma sorted_range_ext :
  forall l l1 left right,
    0 <= left ->
    right < Zlength l ->
    Zlength l = Zlength l1 ->
    (forall k, left <= k <= right -> Znth k l1 0 = Znth k l 0) ->
    sorted_range l left right ->
    sorted_range l1 left right.
Proof.
  intros l l1 left right Hleft0 Hrightlen Hlen Heq Hsorted.
  revert l1 Hlen Heq.
  induction Hsorted; intros l1 Hlen Heq.
  - apply sorted_range_base. exact H.
  - apply sorted_range_from_left with (p := p).
    + exact H.
    + eapply partitioned_at_ext.
      * exact Hleft0.
      * exact Hrightlen.
      * exact Hlen.
      * intros k Hk. apply Heq. lia.
      * exact H0.
    + apply IHHsorted.
      * exact Hleft0.
      * pose proof H0 as Hpart0.
        destruct Hpart0 as [Hrange0 _].
        lia.
      * exact Hlen.
      * intros k Hk.
        pose proof H0 as Hpart0.
        destruct Hpart0 as [Hrange0 _].
        apply Heq.
        lia.
  - apply sorted_range_from_right with (p := p).
    + exact H.
    + eapply partitioned_at_ext.
      * exact Hleft0.
      * exact Hrightlen.
      * exact Hlen.
      * intros k Hk. apply Heq. lia.
      * exact H0.
    + apply IHHsorted.
      * pose proof H0 as Hpart0.
        destruct Hpart0 as [Hrange0 _].
        lia.
      * exact Hrightlen.
      * exact Hlen.
      * intros k Hk.
        pose proof H0 as Hpart0.
        destruct Hpart0 as [Hrange0 _].
        apply Heq.
        lia.
  - apply sorted_range_from_both with (p := p).
    + exact H.
    + eapply partitioned_at_ext.
      * exact Hleft0.
      * exact Hrightlen.
      * exact Hlen.
      * intros k Hk. apply Heq. lia.
      * exact H0.
    + apply IHHsorted1.
      * exact Hleft0.
      * pose proof H0 as Hpart0.
        destruct Hpart0 as [Hrange0 _].
        lia.
      * exact Hlen.
      * intros k Hk.
        pose proof H0 as Hpart0.
        destruct Hpart0 as [Hrange0 _].
        apply Heq.
        lia.
    + apply IHHsorted2.
      * pose proof H0 as Hpart0.
        destruct Hpart0 as [Hrange0 _].
        lia.
      * exact Hrightlen.
      * exact Hlen.
      * intros k Hk.
        pose proof H0 as Hpart0.
        destruct Hpart0 as [Hrange0 _].
        apply Heq.
        lia.
Qed.

Lemma partition_scan_inv_swap :
  forall l l1 low high pivot i j,
    0 <= low ->
    high < Zlength l1 ->
    j < high ->
    low - 1 <= i ->
    i < j ->
    partition_scan_inv l l1 low high pivot i j ->
    Znth j l1 0 <= pivot ->
    partition_scan_inv l
      (replace_Znth j (Znth (i + 1) l1 0)
         (replace_Znth (i + 1) (Znth j l1 0) l1))
      low high pivot (i + 1) (j + 1).
Proof.
  intros l l1 low high pivot i j Hlow Hhigh Hjh Hile Hij
         [Hperm [Hsame [Hpivot [Hle Hgt]]]] Hjle.
  set (l2 :=
    replace_Znth j (Znth (i + 1) l1 0)
      (replace_Znth (i + 1) (Znth j l1 0) l1)).
  assert (Hi1 : 0 <= i + 1 < Zlength l1) by lia.
  assert (Hjrange : 0 <= j < Zlength l1) by lia.
  split.
  - subst l2.
    eapply Permutation_trans.
    + exact Hperm.
    + apply permutation_swap_Znth; lia.
  - split.
    + eapply same_outside_range_trans.
      * exact Hsame.
      * subst l2.
        apply same_outside_range_swap_inside; lia.
    + split.
      * subst l2.
        assert (Hhighj : high <> j) by lia.
        assert (Hhighi1 : high <> i + 1) by lia.
        rewrite (Znth_replace_neq
                   (replace_Znth (i + 1) (Znth j l1 0) l1)
                   high j (Znth (i + 1) l1 0) 0).
        2: { rewrite Zlength_replace_Znth. lia. }
        2: lia.
        2: exact Hhighj.
        rewrite (Znth_replace_neq l1 high (i + 1) (Znth j l1 0) 0).
        2: lia.
        2: lia.
        2: exact Hhighi1.
        exact Hpivot.
      * split.
        -- intros k Hk.
           assert (Hklen : 0 <= k < Zlength l1) by lia.
           destruct (Z.eq_dec k (i + 1)) as [Hki1 | Hki1].
           ++ subst k.
              destruct (Z.eq_dec j (i + 1)) as [Hij1eq | Hij1neq].
              ** subst j.
                 subst l2.
                 rewrite replace_Znth_Znth by lia.
                 rewrite replace_Znth_Znth by lia.
                 exact Hjle.
              ** subst l2.
                 rewrite (Znth_replace_neq
                            (replace_Znth (i + 1) (Znth j l1 0) l1)
                            (i + 1) j (Znth (i + 1) l1 0) 0).
                 2: { rewrite Zlength_replace_Znth. lia. }
                 2: lia.
                 2: { intro HC. apply Hij1neq. symmetry. exact HC. }
                 rewrite (Znth_replace_eq l1 (i + 1) (Znth j l1 0) 0) by lia.
                 exact Hjle.
           ++ assert (Hkj : k <> j) by lia.
              subst l2.
              rewrite (Znth_replace_neq
                         (replace_Znth (i + 1) (Znth j l1 0) l1)
                         k j (Znth (i + 1) l1 0) 0).
              2: { rewrite Zlength_replace_Znth. exact Hklen. }
              2: lia.
              2: exact Hkj.
              rewrite (Znth_replace_neq l1 k (i + 1) (Znth j l1 0) 0).
              2: exact Hklen.
              2: lia.
              2: exact Hki1.
              apply Hle.
              lia.
        -- intros k Hk.
           assert (Hklen : 0 <= k < Zlength l1) by lia.
           subst l2.
           destruct (Z.eq_dec k j) as [Hkj | Hkj].
           ++ subst k.
              rewrite (Znth_replace_eq
                         (replace_Znth (i + 1) (Znth j l1 0) l1)
                         j (Znth (i + 1) l1 0) 0).
              2: { rewrite Zlength_replace_Znth. lia. }
              apply Hgt.
              lia.
           ++ assert (Hki1 : k <> i + 1) by lia.
              rewrite (Znth_replace_neq
                         (replace_Znth (i + 1) (Znth j l1 0) l1)
                         k j (Znth (i + 1) l1 0) 0).
              2: { rewrite Zlength_replace_Znth. exact Hklen. }
              2: lia.
              2: exact Hkj.
              rewrite (Znth_replace_neq l1 k (i + 1) (Znth j l1 0) 0).
              2: exact Hklen.
              2: lia.
              2: exact Hki1.
              apply Hgt.
              lia.
Qed.

Lemma partitioned_at_after_final_swap :
  forall l l1 low high pivot i,
    0 <= low ->
    high < Zlength l1 ->
    low - 1 <= i ->
    i < high ->
    partition_scan_inv l l1 low high pivot i high ->
    partitioned_at
      (replace_Znth high (Znth (i + 1) l1 0)
         (replace_Znth (i + 1) (Znth high l1 0) l1))
      low high (i + 1).
Proof.
  intros l l1 low high pivot i Hlow Hhigh Hile Hihigh
         [_ [_ [Hpivot [Hle Hgt]]]].
  set (l2 :=
    replace_Znth high (Znth (i + 1) l1 0)
      (replace_Znth (i + 1) (Znth high l1 0) l1)).
  assert (Hi1 : 0 <= i + 1 < Zlength l1) by lia.
  assert (Hhighrange : 0 <= high < Zlength l1) by lia.
  assert (Hpiv : Znth (i + 1) l2 0 = pivot).
  {
    subst l2.
    destruct (Z.eq_dec high (i + 1)) as [Heq | Hneq].
    - subst high.
      rewrite replace_Znth_Znth by lia.
      rewrite replace_Znth_Znth by lia.
      exact Hpivot.
    - rewrite (Znth_replace_neq
                 (replace_Znth (i + 1) (Znth high l1 0) l1)
                 (i + 1) high (Znth (i + 1) l1 0) 0).
      2: { rewrite Zlength_replace_Znth. lia. }
      2: lia.
      2: { intro HC. apply Hneq. symmetry. exact HC. }
      rewrite (Znth_replace_eq l1 (i + 1) (Znth high l1 0) 0) by lia.
      exact Hpivot.
  }
  split.
  - lia.
  - split.
    + apply Forall_sublist_by_Znth.
      * lia.
      * subst l2. rewrite !Zlength_replace_Znth. lia.
      * intros k Hk.
        rewrite Hpiv.
        assert (Hklen : 0 <= k < Zlength l1) by lia.
        assert (Hkhigh : k <> high) by lia.
        assert (Hki1 : k <> i + 1) by lia.
        subst l2.
        rewrite (Znth_replace_neq
                   (replace_Znth (i + 1) (Znth high l1 0) l1)
                   k high (Znth (i + 1) l1 0) 0).
        2: { rewrite Zlength_replace_Znth. exact Hklen. }
        2: lia.
        2: exact Hkhigh.
        rewrite (Znth_replace_neq l1 k (i + 1) (Znth high l1 0) 0).
        2: exact Hklen.
        2: lia.
        2: exact Hki1.
        apply Hle.
        lia.
    + apply Forall_sublist_by_Znth.
      * lia.
      * subst l2. rewrite !Zlength_replace_Znth. lia.
      * intros k Hk.
        rewrite Hpiv.
        assert (Hklen : 0 <= k < Zlength l1) by lia.
        destruct (Z.eq_dec k high) as [Hkhigh | Hkhigh].
        -- subst k.
           subst l2.
           rewrite (Znth_replace_eq
                      (replace_Znth (i + 1) (Znth high l1 0) l1)
                      high (Znth (i + 1) l1 0) 0).
           2: { rewrite Zlength_replace_Znth. lia. }
           apply Hgt.
           lia.
        -- assert (Hki1 : k <> i + 1) by lia.
           subst l2.
           rewrite (Znth_replace_neq
                      (replace_Znth (i + 1) (Znth high l1 0) l1)
                      k high (Znth (i + 1) l1 0) 0).
           2: { rewrite Zlength_replace_Znth. exact Hklen. }
           2: lia.
           2: exact Hkhigh.
           rewrite (Znth_replace_neq l1 k (i + 1) (Znth high l1 0) 0).
           2: exact Hklen.
           2: lia.
           2: exact Hki1.
           apply Hgt.
           lia.
Qed.

Lemma proof_of_swap_return_wit_1 : swap_return_wit_1.
Proof.
  pre_process.
Qed.

Lemma proof_of_partition_entail_wit_1 : partition_entail_wit_1.
Proof.
  pre_process.
  Exists l.
  entailer!.
  unfold partition_scan_inv.
  split.
  - apply Permutation_refl.
  - split.
    + apply same_outside_range_refl.
    + split.
      * reflexivity.
      * split.
        -- intros k Hk. lia.
        -- intros k Hk. lia.
Qed.

Lemma proof_of_partition_entail_wit_2_1 : partition_entail_wit_2_1.
Proof.
  pre_process.
  prop_apply (IntArray.full_length arr_pre n_pre
                (replace_Znth j (Znth (i + 1) l1_2 0)
                   (replace_Znth (i + 1) (Znth j l1_2 0) l1_2))).
  Intros.
  Exists (replace_Znth j (Znth (i + 1) l1_2 0)
            (replace_Znth (i + 1) (Znth j l1_2 0) l1_2)).
  entailer!.
  eapply partition_scan_inv_swap; eauto.
  - match goal with
    | Hlen_swapped : Z.of_nat (length _) = n_pre |- _ =>
        rewrite <- Zlength_correct in Hlen_swapped;
        rewrite !Zlength_replace_Znth in Hlen_swapped;
        lia
    end.
Qed.

Lemma proof_of_partition_entail_wit_2_2 : partition_entail_wit_2_2.
Proof.
  pre_process.
  Exists l1_2.
  entailer!.
  unfold partition_scan_inv in *.
  destruct PreH10 as [Hperm [Hsame [Hpivot [Hle Hgt]]]].
  split.
  - exact Hperm.
  - split.
    + exact Hsame.
    + split.
      * exact Hpivot.
      * split.
        -- intros k Hk. apply Hle. lia.
        -- intros k Hk.
           destruct (Z.eq_dec k j) as [-> | Hneq].
           ++ lia.
           ++ apply Hgt. lia.
Qed.

Lemma proof_of_partition_return_wit_1 : partition_return_wit_1.
Proof.
  pre_process.
  prop_apply (IntArray.full_length arr_pre n_pre
                (replace_Znth high_pre (Znth (i + 1) l1_2 0)
                   (replace_Znth (i + 1) (Znth high_pre l1_2 0) l1_2))).
  Intros.
  Exists (replace_Znth high_pre (Znth (i + 1) l1_2 0)
            (replace_Znth (i + 1) (Znth high_pre l1_2 0) l1_2)).
  entailer!.
  - assert (Hj : j = high_pre) by lia.
    subst j.
    assert (Hlenarr : high_pre < Zlength l1_2).
    {
      match goal with
      | Hlen_swapped : Z.of_nat (length _) = n_pre |- _ =>
          rewrite <- Zlength_correct in Hlen_swapped;
          rewrite !Zlength_replace_Znth in Hlen_swapped;
          lia
      end.
    }
    eapply partitioned_at_after_final_swap; eauto; lia.
  - destruct PreH9 as [_ [Hsame _]].
    assert (Hlenarr : high_pre < Zlength l1_2).
    {
      match goal with
      | Hlen_swapped : Z.of_nat (length _) = n_pre |- _ =>
          rewrite <- Zlength_correct in Hlen_swapped;
          rewrite !Zlength_replace_Znth in Hlen_swapped;
          lia
      end.
    }
    eapply same_outside_range_trans.
    + exact Hsame.
    + apply same_outside_range_swap_inside; lia.
  - destruct PreH9 as [Hperm _].
    assert (Hlenarr : high_pre < Zlength l1_2).
    {
      match goal with
      | Hlen_swapped : Z.of_nat (length _) = n_pre |- _ =>
          rewrite <- Zlength_correct in Hlen_swapped;
          rewrite !Zlength_replace_Znth in Hlen_swapped;
          lia
      end.
    }
    eapply Permutation_trans.
    + exact Hperm.
    + apply permutation_swap_Znth; lia.
Qed.

Lemma proof_of_quicksort_range_return_wit_2 : quicksort_range_return_wit_2.
Proof.
  pre_process.
  prop_apply (IntArray.full_length arr_pre n_pre l1_3).
  Intros.
  Exists l1_3.
  entailer!.
  - assert (Hlen3 : Zlength l1_3 = n_pre).
    { match goal with
      | Hlen : Z.of_nat (length l1_3) = n_pre |- _ =>
          rewrite Zlength_correct; exact Hlen
      end. }
    assert (Hpart : partitioned_at l1_3 left_pre right_pre retval).
    {
      pose proof PreH2 as Hsame23_len.
      destruct Hsame23_len as [Hlen23 _].
      eapply partitioned_at_preserved_by_right; eauto.
      rewrite Hlen23, Hlen3. lia.
    }
    apply sorted_range_from_right with (p := retval).
    + lia.
    + exact Hpart.
    + exact PreH3.
  - assert (Hsame23_full : same_outside_range l1_2 l1_3 left_pre right_pre).
    {
      eapply (same_outside_range_weaken
                l1_2 l1_3 (retval + 1) right_pre left_pre right_pre).
      - lia.
      - lia.
      - exact PreH2.
    }
    eapply same_outside_range_trans.
    + exact PreH9.
    + exact Hsame23_full.
  - eapply Permutation_trans.
    + exact PreH8.
    + exact PreH1.
Qed.

Lemma proof_of_quicksort_range_return_wit_1 : quicksort_range_return_wit_1.
Proof.
  pre_process.
  prop_apply (IntArray.full_length arr_pre n_pre l1_4).
  Intros.
  Exists l1_4.
  entailer!.
  - pose proof PreH2 as Hsame34_len.
    destruct Hsame34_len as [Hlen34 _].
    assert (Hlen4 : Zlength l1_4 = n_pre).
    { match goal with
      | Hlen : Z.of_nat (length l1_4) = n_pre |- _ =>
          rewrite Zlength_correct; exact Hlen
      end. }
    assert (Hpart3 : partitioned_at l1_3 left_pre right_pre retval).
    {
      pose proof PreH6 as Hsame23_len.
      destruct Hsame23_len as [Hlen23 _].
      eapply partitioned_at_preserved_by_left.
      - exact PreH5.
      - exact PreH16.
      - exact PreH6.
      - rewrite Hlen23, Hlen34, Hlen4. lia.
      - exact PreH13.
    }
    assert (Hpart : partitioned_at l1_4 left_pre right_pre retval).
    {
      eapply partitioned_at_preserved_by_right.
      - exact PreH1.
      - exact PreH16.
      - exact PreH2.
      - rewrite Hlen34, Hlen4. lia.
      - exact Hpart3.
    }
    assert (Hsorted_left4 : sorted_range l1_4 left_pre (retval - 1)).
    {
      eapply (sorted_range_ext l1_3 l1_4 left_pre (retval - 1)).
      - exact PreH16.
      - rewrite Hlen34, Hlen4. lia.
      - exact Hlen34.
      - intros k Hk.
        destruct PreH2 as [_ Heq34].
        apply Heq34.
        + rewrite Hlen34, Hlen4. lia.
        + left. lia.
      - exact PreH7.
    }
    apply sorted_range_from_both with (p := retval).
    + lia.
    + exact Hpart.
    + exact Hsorted_left4.
    + exact PreH3.
  - assert (Hsame23_full : same_outside_range l1_2 l1_3 left_pre right_pre).
    {
      eapply (same_outside_range_weaken
                l1_2 l1_3 left_pre (retval - 1) left_pre right_pre).
      - lia.
      - lia.
      - exact PreH6.
    }
    assert (Hsame34_full : same_outside_range l1_3 l1_4 left_pre right_pre).
    {
      eapply (same_outside_range_weaken
                l1_3 l1_4 (retval + 1) right_pre left_pre right_pre).
      - lia.
      - lia.
      - exact PreH2.
    }
    eapply same_outside_range_trans.
    + exact PreH12.
    + eapply same_outside_range_trans.
      * exact Hsame23_full.
      * exact Hsame34_full.
  - eapply Permutation_trans.
    + exact PreH11.
    + eapply Permutation_trans.
      * exact PreH5.
      * exact PreH1.
Qed.

Lemma proof_of_quicksort_range_return_wit_3 : quicksort_range_return_wit_3.
Proof.
  pre_process.
  prop_apply (IntArray.full_length arr_pre n_pre l1_3).
  Intros.
  Exists l1_3.
  entailer!.
  - pose proof PreH3 as Hsame23_len.
    destruct Hsame23_len as [Hlen23 _].
    assert (Hlen3 : Zlength l1_3 = n_pre).
    { match goal with
      | Hlen : Z.of_nat (length l1_3) = n_pre |- _ =>
          rewrite Zlength_correct; exact Hlen
      end. }
    assert (Hpart : partitioned_at l1_3 left_pre right_pre retval).
    {
      assert (Hrightlen : right_pre < Zlength l1_2).
      { rewrite Hlen23, Hlen3. lia. }
      eapply (partitioned_at_preserved_by_left
                l1_2 l1_3 left_pre right_pre retval).
      - exact PreH2.
      - exact PreH13.
      - exact PreH3.
      - exact Hrightlen.
      - exact PreH10.
    }
    apply sorted_range_from_left with (p := retval).
    + lia.
    + exact Hpart.
    + exact PreH4.
  - assert (Hsame23_full : same_outside_range l1_2 l1_3 left_pre right_pre).
    {
      eapply (same_outside_range_weaken
                l1_2 l1_3 left_pre (retval - 1) left_pre right_pre).
      - lia.
      - lia.
      - exact PreH3.
    }
    eapply same_outside_range_trans.
    + exact PreH9.
    + exact Hsame23_full.
  - eapply Permutation_trans.
    + exact PreH8.
    + exact PreH2.
Qed.

Lemma proof_of_quicksort_range_return_wit_4 : quicksort_range_return_wit_4.
Proof.
  pre_process.
  Exists l.
  entailer!.
  - apply sorted_range_base. lia.
  - apply same_outside_range_refl.
Qed.

Lemma proof_of_int_array_quicksort_return_wit_1 : int_array_quicksort_return_wit_1.
Proof.
  pre_process.
  prop_apply (IntArray.full_length arr_pre n_pre l1_2).
  Intros.
  Exists l1_2.
  entailer!.
  eapply sorted_range_implies_increasing.
  rewrite Zlength_correct.
  match goal with
  | Hlen : Z.of_nat (length l1_2) = n_pre |- _ =>
      rewrite Hlen
  end.
  exact PreH3.
Qed.
