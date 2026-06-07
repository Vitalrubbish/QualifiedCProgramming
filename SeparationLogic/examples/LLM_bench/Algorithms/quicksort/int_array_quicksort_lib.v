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
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Import ListNotations.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Local Open Scope sac.

Definition permutation : list Z -> list Z -> Prop := @Permutation Z.

Fixpoint increasing_aux (l: list Z) (x: Z): Prop :=
  match l with
  | nil => True
  | y :: l0 => x <= y /\ increasing_aux l0 y
  end.

Definition increasing (l: list Z): Prop :=
  match l with
  | nil => True
  | x :: l0 => increasing_aux l0 x
  end.

Definition same_outside_range (l l1: list Z) (left right: Z) : Prop :=
  Zlength l = Zlength l1 /\
  forall k,
    0 <= k < Zlength l ->
    k < left \/ right < k ->
    Znth k l1 0 = Znth k l 0.

Definition partitioned_at (l: list Z) (low high p: Z) : Prop :=
  low <= p <= high /\
  Forall (fun x => x <= Znth p l 0) (sublist low p l) /\
  Forall (fun x => Znth p l 0 < x) (sublist (p + 1) (high + 1) l).

Definition partition_scan_inv (l l1: list Z) (low high pivot i j: Z) : Prop :=
  permutation l l1 /\
  same_outside_range l l1 low high /\
  Znth high l1 0 = pivot /\
  (forall k, low <= k <= i -> Znth k l1 0 <= pivot) /\
  (forall k, i < k < j -> pivot < Znth k l1 0).

Inductive sorted_range (l: list Z) (left right: Z) : Prop :=
| sorted_range_base :
    left >= right ->
    sorted_range l left right
| sorted_range_from_left : forall p,
    p >= right ->
    partitioned_at l left right p ->
    sorted_range l left (p - 1) ->
    sorted_range l left right
| sorted_range_from_right : forall p,
    p <= left ->
    partitioned_at l left right p ->
    sorted_range l (p + 1) right ->
    sorted_range l left right
| sorted_range_from_both : forall p,
    left <= p <= right ->
    partitioned_at l left right p ->
    sorted_range l left (p - 1) ->
    sorted_range l (p + 1) right ->
    sorted_range l left right.

Definition incr (l: list Z) : Prop :=
  increasing l.

Definition ordered_range (l: list Z) (left right: Z) : Prop :=
  forall i j, left <= i -> i <= j -> j <= right -> Znth i l 0 <= Znth j l 0.

Lemma Forall_Znth_range :
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

Lemma Forall_sublist_by_Znth_range :
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

Lemma increasing_aux_tail_increasing :
  forall l x,
    increasing_aux l x ->
    increasing l.
Proof.
  intros l x Hinc.
  destruct l; simpl; auto.
  destruct Hinc as [_ Hrest].
  exact Hrest.
Qed.

Lemma increasing_aux_head_le_all :
  forall l x k,
    increasing_aux l x ->
    0 <= k < Zlength l ->
    x <= Znth k l 0.
Proof.
  induction l; intros x k Hinc Hk.
  - rewrite Zlength_nil in Hk. lia.
  - simpl in Hinc.
    destruct Hinc as [Hxa Hrest].
    destruct (Z.eq_dec k 0) as [-> | Hneq].
    + reflexivity || exact Hxa.
    + rewrite Znth_cons by lia.
      eapply Z.le_trans.
      * exact Hxa.
      * apply IHl with (x := a); auto.
      rewrite Zlength_cons in Hk.
      lia.
Qed.

Lemma increasing_implies_ordered_full :
  forall l,
    increasing l ->
    ordered_range l 0 (Zlength l - 1).
Proof.
  induction l; intros Hinc i j Hi Hij Hj.
  - rewrite Zlength_nil in Hj. lia.
  - rewrite Zlength_cons in Hj.
    destruct (Z.eq_dec i 0) as [-> | Hineq].
    + destruct (Z.eq_dec j 0) as [-> | Hjneq].
      * reflexivity.
      * rewrite (@Znth_cons Z 0 j a l) by lia.
        apply increasing_aux_head_le_all with (x := a); auto.
        split; lia.
    + assert (0 < i) by lia.
      assert (0 < j) by lia.
      rewrite !Znth_cons by lia.
      apply IHl.
      * apply increasing_aux_tail_increasing with (x := a). exact Hinc.
      * lia.
      * lia.
      * lia.
Qed.

Lemma ordered_range_full_implies_increasing :
  forall l,
    ordered_range l 0 (Zlength l - 1) ->
    increasing l.
Proof.
  induction l; intros Hord; simpl.
  - exact I.
  - destruct l.
    + exact I.
    + split.
      * assert (Hhead : Znth 0 (a :: z :: l) 0 <= Znth 1 (a :: z :: l) 0).
        {
          assert (Hbound0 : 1 <= Zlength (z :: l)).
          {
            rewrite Zlength_cons.
            pose proof Zlength_nonneg l.
            lia.
          }
          assert (Hbound : 1 <= Zlength (a :: z :: l) - 1).
          {
            rewrite Zlength_cons.
            lia.
          }
          specialize (Hord 0 1 ltac:(lia) ltac:(lia) Hbound).
          exact Hord.
        }
        exact Hhead.
      * apply IHl.
        intros i j Hi Hij Hj.
        assert (Hshift :
          Znth (i + 1) (a :: z :: l) 0 <= Znth (j + 1) (a :: z :: l) 0).
        {
          assert (Hj' : j + 1 <= Zlength (a :: z :: l) - 1).
          {
            rewrite Zlength_cons.
            lia.
          }
          apply Hord.
          - lia.
          - lia.
          - exact Hj'.
        }
        rewrite (@Znth_cons Z 0 (i + 1) a (z :: l)) in Hshift by lia.
        rewrite (@Znth_cons Z 0 (j + 1) a (z :: l)) in Hshift by lia.
        replace (i + 1 - 1) with i in Hshift by lia.
        replace (j + 1 - 1) with j in Hshift by lia.
        exact Hshift.
Qed.

Lemma partitioned_at_left_Znth_le :
  forall l left right p k,
    0 <= left ->
    p <= Zlength l ->
    partitioned_at l left right p ->
    left <= k < p ->
    Znth k l 0 <= Znth p l 0.
Proof.
  intros l left right p k Hleft0 Hp Hpart Hk.
  destruct Hpart as [_ [Hleft _]].
  pose proof (Forall_Znth_range
                (fun x => x <= Znth p l 0)
                (sublist left p l)
                (k - left) 0 Hleft) as Hz.
  assert (Hk' : 0 <= k - left < Zlength (sublist left p l)).
  {
    rewrite Zlength_sublist by lia.
    lia.
  }
  specialize (Hz Hk').
  rewrite (@Znth_sublist_lt Z 0 left p l (k - left)) in Hz.
  2: lia.
  2: { exact Hp. }
  2: {
    rewrite Zlength_sublist in Hk' by lia.
    exact Hk'.
  }
  replace (left + (k - left)) with k in Hz by lia.
  exact Hz.
Qed.

Lemma partitioned_at_right_Znth_lt :
  forall l left right p k,
    0 <= left ->
    right < Zlength l ->
    partitioned_at l left right p ->
    p < k <= right ->
    Znth p l 0 < Znth k l 0.
Proof.
  intros l left right p k Hleft0 Hrightlen Hpart Hk.
  destruct Hpart as [Hprange [_ Hright]].
  pose proof (Forall_Znth_range
                (fun x => Znth p l 0 < x)
                (sublist (p + 1) (right + 1) l)
                (k - (p + 1)) 0 Hright) as Hz.
  assert (Hk' : 0 <= k - (p + 1) < Zlength (sublist (p + 1) (right + 1) l)).
  {
    rewrite Zlength_sublist by lia.
    lia.
  }
  specialize (Hz Hk').
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

Lemma sorted_range_implies_ordered_range :
  forall l left right,
    0 <= left ->
    right < Zlength l ->
    sorted_range l left right ->
    ordered_range l left right.
Proof.
  intros l left right Hleft0 Hrightlen Hsorted.
  induction Hsorted; intros i j Hi Hij Hj.
  - assert (i = j) by lia.
    subst j.
    reflexivity.
  - pose proof H0 as Hpart.
    destruct H0 as [[Hp_left Hp_right] _].
    assert (p = right) by lia.
    subst p.
    destruct (Z.eq_dec j right) as [-> | Hjneq].
    + destruct (Z.eq_dec i right) as [-> | Hineq].
      * reflexivity.
      * eapply partitioned_at_left_Znth_le.
        -- exact Hleft0.
        -- lia.
        -- exact Hpart.
        -- lia.
    + eapply IHHsorted; eauto; lia.
  - pose proof H0 as Hpart.
    destruct H0 as [[Hp_left Hp_right] _].
    assert (p = left) by lia.
    subst p.
    destruct (Z.eq_dec i left) as [-> | Hineq].
    + destruct (Z.eq_dec j left) as [-> | Hjneq].
      * reflexivity.
      * apply Z.lt_le_incl.
        eapply partitioned_at_right_Znth_lt.
        -- exact Hleft0.
        -- exact Hrightlen.
        -- exact Hpart.
        -- lia.
    + eapply IHHsorted; eauto; lia.
  - pose proof H0 as Hpart.
    destruct H0 as [[Hp_left Hp_right] _].
    destruct (Z_lt_ge_dec j p) as [Hjp | Hpj].
    + eapply IHHsorted1; eauto; lia.
    + destruct (Z_gt_le_dec i p) as [Hip | Hpi].
      * eapply IHHsorted2; eauto; lia.
      * assert (Hip_cases : i = p \/ i < p) by lia.
        assert (Hj_cases : j = p \/ p < j) by lia.
        destruct Hip_cases as [-> | Hip'].
        {
          destruct Hj_cases as [-> | Hpj'].
          - reflexivity.
          - apply Z.lt_le_incl.
            eapply partitioned_at_right_Znth_lt.
            + exact Hleft0.
            + exact Hrightlen.
            + exact Hpart.
            + lia.
        }
        {
          destruct Hj_cases as [-> | Hpj'].
          - eapply partitioned_at_left_Znth_le.
            + exact Hleft0.
            + eapply Z.le_trans.
              * exact Hp_right.
              * apply Z.lt_le_incl. exact Hrightlen.
            + exact Hpart.
            + lia.
          - eapply Z.le_trans.
            + eapply partitioned_at_left_Znth_le.
              * exact Hleft0.
              * eapply Z.le_trans.
                { exact Hp_right. }
                { apply Z.lt_le_incl. exact Hrightlen. }
              * exact Hpart.
              * lia.
            + apply Z.lt_le_incl.
              eapply partitioned_at_right_Znth_lt.
              * exact Hleft0.
              * exact Hrightlen.
              * exact Hpart.
              * lia.
        }
Qed.

Lemma ordered_range_implies_sorted_range :
  forall l left right,
    0 <= left ->
    right < Zlength l ->
    ordered_range l left right ->
    sorted_range l left right.
Proof.
  intros l.
  assert (Hind :
    forall n left right,
      Z.to_nat (right - left + 1) = n ->
      0 <= left ->
      right < Zlength l ->
      ordered_range l left right ->
      sorted_range l left right).
  {
    induction n; intros left right Hn Hleft Hright Hord.
    - apply sorted_range_base.
      destruct (Z_ge_dec left right) as [Hge | Hlt].
      + exact Hge.
      + assert (Hz : Z.of_nat (Z.to_nat (right - left + 1)) = right - left + 1).
        { rewrite Z2Nat.id by lia. reflexivity. }
        rewrite Hn in Hz. simpl in Hz. lia.
    - destruct (Z_ge_dec left right) as [Hge | Hlt].
      + apply sorted_range_base. exact Hge.
      + apply sorted_range_from_left with (p := right).
        * lia.
        * split.
          -- lia.
          -- split.
             ++ apply Forall_sublist_by_Znth_range.
                ** lia.
                ** lia.
                ** intros k Hk.
                   apply Hord; lia.
             ++ rewrite Zsublist_nil by lia.
                constructor.
        * apply IHn with (left := left) (right := right - 1).
          -- replace ((right - 1) - left + 1) with (right - left) by lia.
             replace (right - left + 1) with ((right - left) + 1) in Hn by lia.
             rewrite Z2Nat.inj_add in Hn by lia.
             simpl in Hn.
             lia.
          -- exact Hleft.
          -- lia.
          -- intros i j Hi Hij Hj.
             apply Hord; lia.
  }
  intros left right Hleft Hright Hord.
  apply (Hind (Z.to_nat (right - left + 1)) left right); auto.
Qed.

Lemma sorted_range_implies_increasing :
  forall l,
    sorted_range l 0 (Zlength l - 1) ->
    increasing l.
Proof.
  intros l Hsorted.
  apply ordered_range_full_implies_increasing.
  eapply sorted_range_implies_ordered_range.
  - lia.
  - pose proof (Zlength_nonneg l).
    lia.
  - exact Hsorted.
Qed.

Lemma increasing_implies_sorted_range :
  forall l,
    increasing l ->
    sorted_range l 0 (Zlength l - 1).
Proof.
  intros l Hinc.
  apply ordered_range_implies_sorted_range.
  - lia.
  - destruct l; rewrite ?Zlength_nil, ?Zlength_cons; lia.
  - apply increasing_implies_ordered_full.
    exact Hinc.
Qed.

Lemma increasing_iff_sorted_range :
  forall l,
    increasing l <-> sorted_range l 0 (Zlength l - 1).
Proof.
  intros l.
  split.
  - apply increasing_implies_sorted_range.
  - apply sorted_range_implies_increasing.
Qed.

Lemma replace_nth_length_Z :
  forall m (a: Z) (l0: list Z),
    length (replace_nth m l0 a) = length l0.
Proof.
  intros m a l0.
  revert l0.
  induction m; intros l0; destruct l0; simpl; try reflexivity.
  rewrite IHm.
  reflexivity.
Qed.

Lemma Zlength_replace_Znth :
  forall n (a: Z) l,
    Zlength (replace_Znth n a l) = Zlength l.
Proof.
  intros n a l.
  rewrite !Zlength_correct.
  unfold replace_Znth.
  rewrite replace_nth_length_Z.
  reflexivity.
Qed.

Lemma increasing_length_le_1 :
  forall l,
    Zlength l <= 1 ->
    increasing l.
Proof.
  intros l Hlen.
  unfold increasing.
  destruct l as [ | a l' ]; simpl; auto.
  destruct l' as [ | b l'' ]; simpl.
  - auto.
  - rewrite Zlength_correct in Hlen.
    simpl in Hlen.
    lia.
Qed.

Lemma replace_Znth_swap_form :
  forall (l1 l2 l3: list Z) (xi xj: Z),
    replace_Znth (Zlength l1 + 1 + Zlength l2) xi
      (replace_Znth (Zlength l1) xj (l1 ++ xi :: l2 ++ xj :: l3)) =
    l1 ++ xj :: l2 ++ xi :: l3.
Proof.
  intros.
  pose proof (Zlength_nonneg l2) as Hlen2.
  set (n1 := Zlength l1).
  set (n2 := Zlength l1 + 1 + Zlength l2).
  rewrite replace_Znth_app_r with (l1 := l1) (l2 := (xi :: l2 ++ xj :: l3)) by (subst n1; lia).
  rewrite (replace_Znth_nothing (A := Z) n1 l1 xj) by (subst n1; lia).
  replace (n1 - Zlength l1) with 0 by (subst n1; lia).
  assert (H0: replace_Znth 0 xj (xi :: l2 ++ xj :: l3) = xj :: l2 ++ xj :: l3) by reflexivity.
  rewrite H0.
  rewrite replace_Znth_app_r with (l1 := l1) (l2 := (xj :: l2 ++ xj :: l3)) by (subst n2; lia).
  rewrite (replace_Znth_nothing (A := Z) (n1 + 1 + Zlength l2) l1 xi) by (subst n1; lia).
  replace (n1 + 1 + Zlength l2 - Zlength l1) with (1 + Zlength l2) by (subst n1; lia).
  rewrite replace_Znth_cons by lia.
  replace (1 + Zlength l2 - 1) with (Zlength l2) by lia.
  rewrite replace_Znth_app_r with (l1 := l2) (l2 := (xj :: l3)) by lia.
  rewrite (replace_Znth_nothing (A := Z) (Zlength l2) l2 xi) by lia.
  replace (Zlength l2 - Zlength l2) with 0 by lia.
  assert (H1: replace_Znth 0 xi (xj :: l3) = xi :: l3) by reflexivity.
  rewrite H1.
  reflexivity.
Qed.

Lemma permutation_swap_Znth_lt :
  forall (l: list Z) i j (d: Z),
    0 <= i /\ i < j /\ j < Zlength l ->
    permutation l (replace_Znth j (Znth i l d) (replace_Znth i (Znth j l d) l)).
Proof.
  intros l i j d Hrange.
  unfold permutation.
  destruct Hrange as [ Hi [ Hij Hj ] ].
  remember (Znth i l d) as xi0.
  remember (Znth j l d) as xj0.
  set (ni := Z.to_nat i).
  set (nj := Z.to_nat (j - i - 1)).
  set (l1 := firstn ni l).
  set (lr := skipn (S ni) l).
  set (l2 := firstn nj lr).
  set (l3 := skipn (S nj) lr).
  assert (Hsplit_i: l = l1 ++ xi0 :: lr).
  {
    subst l1 lr ni.
    rewrite (list_split_nth _ (Z.to_nat i) l d) at 1.
    2:{ rewrite Zlength_correct in Hj. lia. }
    rewrite Heqxi0.
    reflexivity.
  }
  assert (Hj_lr: (nj < length lr)%nat).
  {
    subst nj lr ni.
    rewrite length_skipn.
    rewrite Zlength_correct in Hj.
    lia.
  }
  assert (Hsplit_j: lr = l2 ++ xj0 :: l3).
  {
    subst l2 l3.
    rewrite (list_split_nth _ nj lr d) at 1 by exact Hj_lr.
    replace xj0 with (nth nj lr d).
    2:{
      subst nj lr ni.
      rewrite Heqxj0.
      unfold Znth.
      rewrite nth_skipn.
      assert (Hnat: (Z.to_nat (j - i - 1) + S (Z.to_nat i))%nat = Z.to_nat j).
      {
        apply Nat2Z.inj.
        rewrite Nat2Z.inj_add.
        rewrite Nat2Z.inj_succ.
        repeat rewrite Z2Nat.id by lia.
        lia.
	      }
	      rewrite <- Hnat.
	      replace (S (Z.to_nat i) + Z.to_nat (j - i - 1))%nat
	        with (Z.to_nat (j - i - 1) + S (Z.to_nat i))%nat by lia.
	      reflexivity.
	    }
    reflexivity.
  }
  assert (Hl: l = l1 ++ xi0 :: l2 ++ xj0 :: l3).
  {
    rewrite Hsplit_j in Hsplit_i.
    exact Hsplit_i.
  }
  replace l with (l1 ++ xi0 :: l2 ++ xj0 :: l3) by (symmetry; exact Hl).
  replace i with (Zlength l1).
  2:{
    subst l1 ni.
    rewrite Zlength_correct, length_firstn.
    rewrite Zlength_correct in Hj.
    rewrite Nat.min_l by lia.
    lia.
  }
  replace j with (Zlength l1 + 1 + Zlength l2).
  2:{
    subst l1 l2 lr ni nj.
    rewrite !Zlength_correct.
    rewrite !length_firstn.
    rewrite length_skipn.
    rewrite Zlength_correct in Hj.
    lia.
  }
  rewrite replace_Znth_swap_form.
  eapply Permutation_trans.
  2:{ reflexivity. }
  apply Permutation_app_head.
  eapply Permutation_trans.
  - apply Permutation_middle.
  - eapply Permutation_trans.
    + apply Permutation_app_head.
      apply perm_swap.
    + apply Permutation_sym.
      apply Permutation_middle.
Qed.

Lemma replace_nth_comm_Z :
  forall ni nj (l: list Z) a b,
    ni <> nj ->
    replace_nth nj (replace_nth ni l a) b =
    replace_nth ni (replace_nth nj l b) a.
Proof.
  intros ni nj l a b Hneq.
  revert nj l Hneq.
  induction ni; intros nj l Hneq; destruct l as [ | x xs ]; simpl.
  - destruct nj; reflexivity.
  - destruct nj; simpl.
    + contradiction Hneq; reflexivity.
    + reflexivity.
  - destruct nj; reflexivity.
  - destruct nj; simpl.
    + reflexivity.
    + f_equal.
      apply IHni.
      intros Heq.
      apply Hneq.
      now f_equal.
Qed.

Lemma replace_Znth_comm :
  forall (l: list Z) i j (a b: Z),
    0 <= i ->
    0 <= j ->
    i <> j ->
    replace_Znth j b (replace_Znth i a l) =
    replace_Znth i a (replace_Znth j b l).
Proof.
  intros l i j a b Hi Hj Hneq.
  unfold replace_Znth.
  apply replace_nth_comm_Z.
  intro Heq.
  apply Hneq.
  apply Z2Nat.inj in Heq; lia.
Qed.

Lemma permutation_swap_Znth :
  forall (l: list Z) i j (d: Z),
    0 <= i < Zlength l ->
    0 <= j < Zlength l ->
    permutation l (replace_Znth j (Znth i l d) (replace_Znth i (Znth j l d) l)).
Proof.
  intros l i j d Hi Hj.
  destruct (Z_lt_ge_dec i j) as [ Hij | Hge ].
  - apply permutation_swap_Znth_lt.
    lia.
  - destruct (Z_lt_ge_dec j i) as [ Hji | Heq ].
    + eapply Permutation_trans.
      2:{
        apply Permutation_refl.
      }
      rewrite replace_Znth_comm by lia.
      apply permutation_swap_Znth_lt.
      lia.
    + assert (i = j) by lia.
      subst j.
      unfold permutation.
      rewrite replace_Znth_Znth by lia.
      rewrite replace_Znth_Znth by lia.
      apply Permutation_refl.
Qed.

Lemma permutation_swap_Znth_by_result_length :
  forall (l: list Z) i j n (d: Z),
    0 <= i < n ->
    0 <= j < n ->
    Zlength (replace_Znth j (Znth i l d) (replace_Znth i (Znth j l d) l)) = n ->
    permutation l (replace_Znth j (Znth i l d) (replace_Znth i (Znth j l d) l)).
Proof.
  intros l i j n d Hi Hj Hlen.
  assert (Zlength l = n).
  {
    rewrite <- Zlength_replace_Znth with (n := i) (a := Znth j l d).
    rewrite <- Zlength_replace_Znth with (n := j) (a := Znth i l d).
    exact Hlen.
  }
  apply permutation_swap_Znth; lia.
Qed.
