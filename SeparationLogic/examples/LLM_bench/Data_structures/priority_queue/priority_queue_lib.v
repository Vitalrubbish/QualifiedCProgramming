Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import ListLib.
From MaxMinLib Require Import MaxMin Interface.

Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope list_scope.

Definition HeapParent (child : Z) : Z :=
  Z.quot (child - 1) 2.

Definition PrefixMaxValue (l : list Z) (n ans : Z) : Prop :=
  0 < n /\
  n <= Zlength l /\
  max_value_of_subset Z.le
    (fun idx => 0 <= idx /\ idx < n)
    (fun idx => Znth idx l 0)
    ans.

Definition MaxHeapPrefix (l : list Z) (n : Z) : Prop :=
  0 <= n /\
  n <= Zlength l /\
  forall child,
    0 < child /\ child < n ->
    Znth (HeapParent child) l 0 >= Znth child l 0.

Definition PriorityQueuePrefix (l : list Z) (n : Z) : Prop :=
  MaxHeapPrefix l n /\
  (0 < n -> PrefixMaxValue l n (Znth 0 l 0)).

Definition SameElementsPrefix (before after : list Z) (n : Z) : Prop :=
  0 <= n /\
  n <= Zlength before /\
  n <= Zlength after /\
  Permutation (sublist 0 n before) (sublist 0 n after).

Definition HeapOrderExceptUp (l : list Z) (size child : Z) : Prop :=
  0 <= child /\
  child < size /\
  forall node,
    0 < node /\ node < size /\ node <> child ->
    Znth (HeapParent node) l 0 >= Znth node l 0.

Definition PushHoleChildrenPreserved (l : list Z) (n child : Z) : Prop :=
  forall node,
    0 < node /\ node < n + 1 /\ HeapParent node = child ->
    Znth (HeapParent child) l 0 >= Znth node l 0.

Definition PushLoopState
    (before cur : list Z) (n child x : Z) : Prop :=
  0 <= n /\
  Zlength before = n + 1 /\
  Zlength cur = n + 1 /\
  0 <= child /\
  child <= n /\
  Znth n before 0 = x /\
  Znth child cur 0 = x /\
  MaxHeapPrefix before n /\
  Permutation before cur /\
  HeapOrderExceptUp cur (n + 1) child /\
  PushHoleChildrenPreserved cur n child.

Definition PushResult
    (before after : list Z) (n x : Z) : Prop :=
  0 <= n /\
  Zlength before = n + 1 /\
  Zlength after = n + 1 /\
  Znth n before 0 = x /\
  MaxHeapPrefix before n /\
  PriorityQueuePrefix after (n + 1) /\
  Permutation before after.

Definition BuildPrefixState
    (before cur : list Z) (processed : Z) : Prop :=
  1 <= processed /\
  processed <= Zlength before /\
  Zlength cur = Zlength before /\
  PriorityQueuePrefix cur processed /\
  SameElementsPrefix before cur processed /\
  sublist processed (Zlength before) cur =
  sublist processed (Zlength before) before.

Definition HeapOrderExceptDown (l : list Z) (size idx : Z) : Prop :=
  0 <= idx /\
  idx < size /\
  forall child,
    0 < child /\ child < size /\ HeapParent child <> idx ->
    Znth (HeapParent child) l 0 >= Znth child l 0.

Definition PopHoleParentDominatesChildren
    (cur : list Z) (size idx : Z) : Prop :=
  idx = 0 \/
  forall child,
    0 < child /\ child < size /\ HeapParent child = idx ->
    Znth (HeapParent idx) cur 0 >= Znth child cur 0.

Definition PopSelectedChild
    (cur : list Z) (size idx largest : Z) : Prop :=
  0 <= idx /\
  idx < size /\
  idx < largest /\
  0 <= largest /\
  largest < size /\
  HeapParent largest = idx /\
  (forall child,
     0 < child /\ child < size /\ HeapParent child = idx ->
     Znth largest cur 0 >= Znth child cur 0).

Definition PopRemainingElements (before cur : list Z) (n : Z) : Prop :=
  1 <= n /\
  n <= Zlength before /\
  n <= Zlength cur /\
  Permutation (sublist 0 (n - 1) cur) (sublist 1 n before).

Definition PopLoopState
    (before cur : list Z) (n idx : Z) : Prop :=
  1 < n /\
  Zlength before = n /\
  Zlength cur = n /\
  0 <= idx /\
  idx < n - 1 /\
  PriorityQueuePrefix before n /\
  Znth idx cur 0 = Znth (n - 1) before 0 /\
  Znth (n - 1) cur 0 = Znth (n - 1) before 0 /\
  PopRemainingElements before cur n /\
  HeapOrderExceptDown cur (n - 1) idx /\
  PopHoleParentDominatesChildren cur (n - 1) idx.

Definition PopReadyState
    (before cur : list Z) (n ret : Z) : Prop :=
  1 < n /\
  Zlength before = n /\
  Zlength cur = n /\
  PriorityQueuePrefix before n /\
  PrefixMaxValue before n ret /\
  ret = Znth 0 before 0 /\
  Znth (n - 1) cur 0 = Znth (n - 1) before 0 /\
  PopRemainingElements before cur n /\
  PriorityQueuePrefix cur (n - 1).

Definition PopResult
    (before after : list Z) (n ret : Z) : Prop :=
  1 <= n /\
  Zlength before = n /\
  Zlength after = n /\
  PriorityQueuePrefix before n /\
  PrefixMaxValue before n ret /\
  ret = Znth 0 before 0 /\
  Znth (n - 1) after 0 = ret /\
  PriorityQueuePrefix after (n - 1) /\
  Permutation before after.

(* Helper imports migrated from priority_queue__pop_final_result_range__merged_proof_manual.v. *)
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Wellfounded.Wellfounded.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.

(* Helper lemmas migrated from priority_queue__pop_final_result_range__merged_proof_manual.v. *)

Lemma heap_parent_bounds_pos : forall child,
  0 < child ->
  0 <= HeapParent child /\ HeapParent child < child.
Proof.
  intros child Hchild.
  unfold HeapParent.
  split.
  - apply Z.quot_pos; lia.
  - apply Z.quot_lt_upper_bound; lia.
Qed.

Lemma priority_queue_prefix_one : forall a,
  1 <= Zlength a ->
  PriorityQueuePrefix a 1.
Proof.
  intros a Hlen.
  unfold PriorityQueuePrefix, MaxHeapPrefix, PrefixMaxValue.
  split.
  - split; [lia|].
    split; [lia|].
    intros child Hchild.
    lia.
  - intros _.
    split; [lia|].
    split; [lia|].
    exists 0.
    split.
    + split.
      * split; lia.
      * intros b Hb.
        destruct Hb as [Hb0 Hb1].
        assert (b = 0) by lia.
        subst b.
        lia.
    + reflexivity.
Qed.

Lemma build_prefix_state_init_one : forall a,
  1 <= Zlength a ->
  BuildPrefixState a a 1.
Proof.
  intros a Hlen.
  unfold BuildPrefixState, SameElementsPrefix.
  split; [lia|].
  split; [lia|].
  split; [reflexivity|].
  split.
  - apply priority_queue_prefix_one; lia.
  - split.
    + split; [lia|].
      split; [lia|].
      split; [lia|apply Permutation_refl].
    + reflexivity.
Qed.

Lemma sublist_prefix_preserves_max_heap : forall l i,
  0 <= i ->
  i < Zlength l ->
  MaxHeapPrefix l i ->
  MaxHeapPrefix (sublist 0 (i + 1) l) i.
Proof.
  intros l i Hi0 Hibound [Hheap0 [Hlen Hord]].
  unfold MaxHeapPrefix.
  split; [lia|].
  split.
  - rewrite Zlength_sublist0 by lia.
    lia.
  - intros child Hchild.
    destruct (heap_parent_bounds_pos child) as [Hparent0 Hparentlt]; try lia.
    rewrite Znth_sublist0 by lia.
    rewrite Znth_sublist0 by lia.
    apply Hord.
    lia.
Qed.

Lemma sublist_prefix_range : forall l n i,
  (forall idx, 0 <= idx < n -> INT_MIN <= Znth idx l 0 <= INT_MAX) ->
  0 <= i ->
  i < n ->
  forall idx, 0 <= idx < i + 1 ->
    INT_MIN <= Znth idx (sublist 0 (i + 1) l) 0 <= INT_MAX.
Proof.
  intros l n i Hrange Hi0 Hilt idx Hidx.
  rewrite Znth_sublist0 by lia.
  apply Hrange.
  lia.
Qed.

Lemma priority_queue_prefix_app_suffix : forall prefix suffix n,
  Zlength prefix = n ->
  PriorityQueuePrefix prefix n ->
  PriorityQueuePrefix (prefix ++ suffix) n.
Proof.
  intros prefix suffix n Hlen [Hheap Hmax].
  split.
  - destruct Hheap as [Hn0 [Hheaplen Hord]].
    unfold MaxHeapPrefix.
    split; [lia|].
    split.
    + rewrite Zlength_app, Hlen.
      pose proof (Zlength_nonneg suffix).
      lia.
    + intros child Hchild.
      destruct (heap_parent_bounds_pos child) as [Hparent0 Hparentlt];
        try lia.
      rewrite app_Znth1 by (rewrite Hlen; lia).
      rewrite app_Znth1 by (rewrite Hlen; lia).
      apply Hord.
      lia.
  - intros Hnpos.
    specialize (Hmax Hnpos).
    unfold PrefixMaxValue in *.
    destruct Hmax as [Hprefix_pos [Hprefix_len [a [[Ha Hdom] Hval]]]].
    destruct Ha as [Ha0 Ha1].
    split; [exact Hprefix_pos|].
    split.
    + rewrite Zlength_app, Hlen.
      pose proof (Zlength_nonneg suffix).
      lia.
    + exists a.
      split.
      * split.
        { split; assumption. }
        { intros b Hb.
          destruct Hb as [Hb0 Hb1].
          rewrite app_Znth1 by (rewrite Hlen; lia).
          rewrite app_Znth1 by (rewrite Hlen; lia).
          apply Hdom.
          split; lia.
        }
      * rewrite app_Znth1 by (rewrite Hlen; lia).
        rewrite app_Znth1 by (rewrite Hlen; lia).
        exact Hval.
Qed.

Lemma build_prefix_state_extend_after_push :
  forall before cur prefix_out i x,
    BuildPrefixState before cur i ->
    i < Zlength before ->
    PushResult (sublist 0 (i + 1) cur) prefix_out i x ->
    BuildPrefixState before
      (prefix_out ++ sublist (i + 1) (Zlength cur) cur) (i + 1).
Proof.
  intros before cur prefix_out i x Hbuild Hilt Hpush.
  destruct Hbuild as
    [Hi1 [Hibound [Hcur_len [HPQcur [Hsame_prefix Hsuffix]]]]].
  destruct Hsame_prefix as [Hi0 [Hbefore_len [Hcur_prefix_len Hperm_prefix]]].
  destruct Hpush as
    [Hi_push [Hprefix_before_len [Hprefix_out_len
      [Hx [Hheap_before [HPQout Hperm_push]]]]]].
  assert (Hi_cur : i < Zlength cur) by lia.
  assert (Hsplit_cur :
    sublist i (Zlength before) cur =
    Znth i cur 0 :: sublist (i + 1) (Zlength before) cur).
  {
    rewrite (sublist_split i (Zlength before) (i + 1) cur) by lia.
    rewrite (sublist_single 0 i cur) by lia.
    simpl.
    reflexivity.
  }
  assert (Hsplit_before :
    sublist i (Zlength before) before =
    Znth i before 0 :: sublist (i + 1) (Zlength before) before).
  {
    rewrite (sublist_split i (Zlength before) (i + 1) before) by lia.
    rewrite (sublist_single 0 i before) by lia.
    simpl.
    reflexivity.
  }
  rewrite Hsuffix in Hsplit_cur.
  rewrite Hsplit_before in Hsplit_cur.
  injection Hsplit_cur as Hnth_eq Hsuffix_tail.
  unfold BuildPrefixState.
  split; [lia|].
  split; [lia|].
  split.
  - rewrite Zlength_app.
    rewrite Zlength_sublist by lia.
    lia.
  - split.
    + apply priority_queue_prefix_app_suffix.
      * exact Hprefix_out_len.
      * exact HPQout.
    + split.
      * unfold SameElementsPrefix.
        split; [lia|].
        split; [lia|].
        split.
        { rewrite Zlength_app.
          rewrite Zlength_sublist by lia.
          lia.
        }
        replace (sublist 0 (i + 1)
          (prefix_out ++ sublist (i + 1) (Zlength cur) cur))
          with prefix_out.
        2:{
          replace (i + 1) with (Zlength prefix_out) by lia.
          symmetry.
          apply sublist_app_exact1.
        }
        eapply Permutation_trans.
        2: exact Hperm_push.
        rewrite (sublist_split 0 (i + 1) i before) by lia.
        rewrite (sublist_split 0 (i + 1) i cur) by lia.
        rewrite (sublist_single 0 i before) by lia.
        rewrite (sublist_single 0 i cur) by lia.
        simpl.
        rewrite Hnth_eq.
        apply Permutation_app_tail.
        exact Hperm_prefix.
      * rewrite sublist_split_app_r with
          (len := i + 1) (l1 := prefix_out)
          (l2 := sublist (i + 1) (Zlength cur) cur).
        2:{ exact Hprefix_out_len. }
        2:{ lia. }
        replace (i + 1 - (i + 1)) with 0 by lia.
        replace (Zlength before - (i + 1))
          with (Zlength (sublist (i + 1) (Zlength cur) cur)).
        2:{
          rewrite Zlength_sublist by lia.
          lia.
        }
        rewrite sublist_self.
        2:{
          rewrite Zlength_sublist by lia.
          reflexivity.
        }
        replace (sublist (i + 1) (Zlength cur) cur)
          with (sublist (i + 1) (Zlength before) cur).
        2:{
          rewrite Hcur_len.
          reflexivity.
        }
        symmetry.
        exact Hsuffix_tail.
Qed.

Lemma max_heap_prefix_root_max : forall a n,
  0 < n ->
  MaxHeapPrefix a n ->
  PrefixMaxValue a n (Znth 0 a 0).
Proof.
  intros a n Hn [Hn0 [Hlen Hord]].
  unfold PrefixMaxValue.
  split; [lia|].
  split; [lia|].
  exists 0.
  split.
  - split.
    + hnf; lia.
    + intros idx Hidx.
      hnf in Hidx.
      destruct Hidx as [Hidx0 Hidxlt].
      enough (Znth idx a 0 <= Znth 0 a 0) by lia.
      refine (well_founded_induction_type
        (A := Z) (R := fun x y => 0 <= x < y)
        (Z.lt_wf 0)
        (fun y => 0 <= y < n -> Znth y a 0 <= Znth 0 a 0)
        _ idx _).
      * intros y IH [Hy0 Hylt].
        destruct (Z.eq_dec y 0) as [-> | Hyneq].
        { lia. }
        assert (0 < y) by lia.
        destruct (heap_parent_bounds_pos y H) as [Hparent0 Hparentlt].
        assert (Hedge: Znth (HeapParent y) a 0 >= Znth y a 0).
        { apply Hord. lia. }
        assert (Hroot_parent: Znth (HeapParent y) a 0 <= Znth 0 a 0).
        { apply IH; lia. }
        lia.
      * lia.
  - reflexivity.
Qed.

Lemma heap_parent_of_left_child : forall idx,
  0 <= idx ->
  HeapParent (2 * idx + 1) = idx.
Proof.
  intros idx Hidx.
  unfold HeapParent.
  replace (2 * idx + 1 - 1) with (2 * idx) by lia.
  replace (2 * idx) with (idx * 2) by lia.
  rewrite Z.quot_mul by lia.
  lia.
Qed.

Lemma heap_parent_of_right_child : forall idx,
  0 <= idx ->
  HeapParent (2 * idx + 2) = idx.
Proof.
  intros idx Hidx.
  unfold HeapParent.
  replace (2 * idx + 2 - 1) with (2 * idx + 1) by lia.
  symmetry.
  apply Z.quot_unique with (r := 1); lia.
Qed.

Lemma heap_parent_child_cases : forall idx child,
  0 <= idx ->
  0 < child ->
  HeapParent child = idx ->
  child = 2 * idx + 1 \/ child = 2 * idx + 2.
Proof.
  intros idx child Hidx Hchild Hparent.
  unfold HeapParent in Hparent.
  assert (Hchild_nonneg : 0 <= child - 1) by lia.
  assert (Hlow : 2 * idx <= child - 1).
  {
    rewrite <- Hparent.
    pose proof (Z.mul_quot_le (child - 1) 2 Hchild_nonneg ltac:(lia))
      as [_ Hlow].
    exact Hlow.
  }
  assert (Hhigh : child - 1 < 2 * (idx + 1)).
  {
    rewrite <- Hparent.
    apply Z.mul_succ_quot_gt; lia.
  }
  lia.
Qed.

Lemma pop_selected_child_right : forall cur size idx left right,
  0 <= idx ->
  left = 2 * idx + 1 ->
  right = left + 1 ->
  right < size ->
  Znth left cur 0 < Znth right cur 0 ->
  PopSelectedChild cur size idx right.
Proof.
  intros cur size idx left right Hidx Hleft Hright Hbound Hcmp.
  subst left right.
  unfold PopSelectedChild.
  split; [lia|].
  split; [lia|].
  split; [lia|].
  split; [lia|].
  split; [lia|].
  split.
  - replace (2 * idx + 1 + 1) with (2 * idx + 2) by lia.
    apply heap_parent_of_right_child; lia.
  - intros child [Hchild_pos [Hchild_lt Hparent]].
    destruct (heap_parent_child_cases idx child Hidx Hchild_pos Hparent)
      as [Hcase | Hcase].
    + subst child.
      lia.
    + subst child.
      replace (2 * idx + 1 + 1) with (2 * idx + 2) in * by lia.
      lia.
Qed.

Lemma pop_selected_child_left_no_right : forall cur size idx left right,
  0 <= idx ->
  left = 2 * idx + 1 ->
  right = left + 1 ->
  left < size ->
  right >= size ->
  PopSelectedChild cur size idx left.
Proof.
  intros cur size idx left right Hidx Hleft Hright Hleft_bound Hright_out.
  subst left right.
  unfold PopSelectedChild.
  split; [lia|].
  split; [lia|].
  split; [lia|].
  split; [lia|].
  split; [lia|].
  split.
  - apply heap_parent_of_left_child; lia.
  - intros child [Hchild_pos [Hchild_lt Hparent]].
    destruct (heap_parent_child_cases idx child Hidx Hchild_pos Hparent)
      as [Hcase | Hcase].
    + subst child.
      lia.
    + subst child.
      replace (2 * idx + 1 + 1) with (2 * idx + 2) in * by lia.
      lia.
Qed.

Lemma pop_selected_child_left_ge_right : forall cur size idx left right,
  0 <= idx ->
  left = 2 * idx + 1 ->
  right = left + 1 ->
  right < size ->
  Znth left cur 0 >= Znth right cur 0 ->
  PopSelectedChild cur size idx left.
Proof.
  intros cur size idx left right Hidx Hleft Hright Hbound Hcmp.
  subst left right.
  unfold PopSelectedChild.
  split; [lia|].
  split; [lia|].
  split; [lia|].
  split; [lia|].
  split; [lia|].
  split.
  - apply heap_parent_of_left_child; lia.
  - intros child [Hchild_pos [Hchild_lt Hparent]].
    destruct (heap_parent_child_cases idx child Hidx Hchild_pos Hparent)
      as [Hcase | Hcase].
    + subst child.
      lia.
    + subst child.
      replace (2 * idx + 1 + 1) with (2 * idx + 2) in * by lia.
      lia.
Qed.

Lemma pop_loop_no_swap_to_ready : forall before cur n idx largest ret,
  PopLoopState before cur n idx ->
  PopSelectedChild cur (n - 1) idx largest ->
  Znth idx cur 0 >= Znth largest cur 0 ->
  PrefixMaxValue before n ret ->
  ret = Znth 0 before 0 ->
  PopReadyState before cur n ret.
Proof.
  intros before cur n idx largest ret Hstate Hsel Hcmp Hprefix Hret.
  destruct Hstate as
    [Hn [Hbefore [Hcur [Hidx0 [Hidxlt [HPQbefore [Hidxval [Hlast [Hremain [Hexcept _]]]]]]]]]].
  destruct Hsel as
    [_ [_ [_ [_ [_ [Hlargest_parent Hlargest_dom]]]]]].
  assert (Hheap_cur : MaxHeapPrefix cur (n - 1)).
  {
    unfold MaxHeapPrefix.
    split; [lia|].
    split; [lia|].
    intros child [Hchild_pos Hchild_lt].
    destruct (Z.eq_dec (HeapParent child) idx) as [Hparent_eq | Hparent_neq].
    - assert (Znth largest cur 0 >= Znth child cur 0).
      { apply Hlargest_dom. lia. }
      rewrite Hparent_eq.
      lia.
    - apply Hexcept.
      lia.
  }
  unfold PopReadyState.
  split; [lia|].
  split; [exact Hbefore|].
  split; [exact Hcur|].
  split; [exact HPQbefore|].
  split; [exact Hprefix|].
  split; [exact Hret|].
  split; [exact Hlast|].
  split; [exact Hremain|].
  split.
  - exact Hheap_cur.
  - intros _.
    apply max_heap_prefix_root_max; try lia.
    exact Hheap_cur.
Qed.

Lemma pop_selected_child_bounds : forall cur size idx left right largest,
  0 <= idx ->
  left = 2 * idx + 1 ->
  right = left + 1 ->
  PopSelectedChild cur size idx largest ->
  0 <= left /\ left < size /\ 0 <= right /\ right <= size.
Proof.
  intros cur size idx left right largest Hidx Hleft Hright Hsel.
  destruct Hsel as
    [_ [_ [Hidxltlargest [_ [Hlargestlt [Hparent _]]]]]].
  assert (Hlargest_pos : 0 < largest) by lia.
  destruct (heap_parent_child_cases idx largest Hidx Hlargest_pos Hparent)
    as [Hcase | Hcase].
  - subst largest.
    subst left right.
    lia.
  - subst largest.
    subst left right.
    lia.
Qed.

Lemma pop_loop_no_child_to_ready : forall before cur n idx ret,
  PopLoopState before cur n idx ->
  idx * 2 + 1 >= n - 1 ->
  PrefixMaxValue before n ret ->
  ret = Znth 0 before 0 ->
  PopReadyState before cur n ret.
Proof.
  intros before cur n idx ret Hstate Hno_child Hprefix Hret.
  destruct Hstate as
    [Hn [Hbefore [Hcur [Hidx0 [Hidxlt [HPQbefore [Hidxval [Hlast [Hremain [Hexcept _]]]]]]]]]].
  assert (Hheap_cur : MaxHeapPrefix cur (n - 1)).
  {
    unfold MaxHeapPrefix.
    split; [lia|].
    split; [lia|].
    intros child [Hchild_pos Hchild_lt].
    destruct (Z.eq_dec (HeapParent child) idx) as [Hparent_eq | Hparent_neq].
    - destruct (heap_parent_child_cases idx child Hidx0 Hchild_pos Hparent_eq)
        as [Hcase | Hcase];
      subst child; lia.
    - apply Hexcept.
      lia.
  }
  unfold PopReadyState.
  split; [lia|].
  split; [exact Hbefore|].
  split; [exact Hcur|].
  split; [exact HPQbefore|].
  split; [exact Hprefix|].
  split; [exact Hret|].
  split; [exact Hlast|].
  split; [exact Hremain|].
  split.
  - exact Hheap_cur.
  - intros _.
    apply max_heap_prefix_root_max; try lia.
    exact Hheap_cur.
Qed.

Lemma push_loop_init_at_tail : forall before n x,
  MaxHeapPrefix before n ->
  Zlength before = n + 1 ->
  Znth n before 0 = x ->
  PushLoopState before before n n x.
Proof.
  intros before n x Hheap Hlen Hx.
  destruct Hheap as [Hn0 [Hheaplen Hord]].
  unfold PushLoopState.
  split; [lia|].
  split; [exact Hlen|].
  split; [exact Hlen|].
  split; [lia|].
  split; [lia|].
  split; [exact Hx|].
  split; [exact Hx|].
  split.
  - split; [exact Hn0|].
    split; [exact Hheaplen|].
    exact Hord.
  - split.
    + apply Permutation_refl.
    + split.
      * unfold HeapOrderExceptUp.
        split; [lia|].
        split; [lia|].
        intros node [Hnodepos [Hnodebound Hneq]].
        apply Hord.
        lia.
      * unfold PushHoleChildrenPreserved.
        intros node [Hnodepos [Hnodebound Hparent]].
        destruct (heap_parent_bounds_pos node Hnodepos) as [_ Hparentlt].
        assert False by (rewrite Hparent in Hparentlt; lia).
        contradiction.
Qed.

Lemma push_loop_root_to_result : forall before cur n x,
  PushLoopState before cur n 0 x ->
  PushResult before cur n x.
Proof.
  intros before cur n x Hstate.
  destruct Hstate as
    [Hn0 [Hlen_before [Hlen_cur [Hchild0 [Hchildn [Hx_before [_ [Hheap_before [Hperm [Hexcept _]]]]]]]]]].
  assert (Hheap_cur: MaxHeapPrefix cur (n + 1)).
  {
    unfold MaxHeapPrefix.
    split; [lia|].
    split; [lia|].
    intros child [Hchildpos Hchildlt].
    apply Hexcept.
    lia.
  }
  unfold PushResult.
  split; [lia|].
  split; [exact Hlen_before|].
  split; [exact Hlen_cur|].
  split; [exact Hx_before|].
  split; [exact Hheap_before|].
  split.
  - split.
    + exact Hheap_cur.
    + intros _.
      apply max_heap_prefix_root_max; try lia.
      exact Hheap_cur.
  - exact Hperm.
Qed.

Lemma push_loop_stop_to_result : forall before cur n child parent x,
  PushLoopState before cur n child x ->
  0 < child ->
  parent = HeapParent child ->
  Znth parent cur 0 >= Znth child cur 0 ->
  PushResult before cur n x.
Proof.
  intros before cur n child parent x Hstate Hchildpos Hparent_eq Hge.
  subst parent.
  destruct Hstate as
    [Hn0 [Hlen_before [Hlen_cur [Hchild0 [Hchildn [Hx_before [_ [Hheap_before [Hperm [Hexcept _]]]]]]]]]].
  assert (Hheap_cur: MaxHeapPrefix cur (n + 1)).
  {
    unfold MaxHeapPrefix.
    split; [lia|].
    split; [lia|].
    intros c [Hcpos Hclt].
    destruct (Z.eq_dec c child) as [-> | Hcneq].
    - exact Hge.
    - apply Hexcept.
      lia.
  }
  unfold PushResult.
  split; [lia|].
  split; [exact Hlen_before|].
  split; [exact Hlen_cur|].
  split; [exact Hx_before|].
  split; [exact Hheap_before|].
  split.
  - split.
    + exact Hheap_cur.
    + intros _.
      apply max_heap_prefix_root_max; try lia.
      exact Hheap_cur.
  - exact Hperm.
Qed.

Lemma list_head_tail_by_sublist : forall (l : list Z) n d,
  0 < n ->
  Zlength l = n ->
  l = Znth 0 l d :: sublist 1 n l.
Proof.
  intros l n d Hn Hlen.
  rewrite <- (sublist_self l n) at 1 by lia.
  rewrite (sublist_split 0 n 1 l) by lia.
  replace (sublist 0 1 l) with (Znth 0 l d :: nil).
  2:{
    replace 1 with (0 + 1) by lia.
    symmetry.
    apply sublist_single.
    lia.
  }
  simpl.
  reflexivity.
Qed.

Lemma pop_loop_state_init_replace_root : forall before n,
  1 < n ->
  Zlength before = n ->
  PriorityQueuePrefix before n ->
  PopLoopState before (replace_Znth 0 (Znth (n - 1) before 0) before) n 0.
Proof.
  intros before n Hn Hlen HPQbefore.
  pose proof HPQbefore as HPQbefore_full.
  destruct HPQbefore as [Hheap_before _].
  destruct Hheap_before as [Hn0 [Hheap_len Hheap_ord]].
  assert (Hbefore_cons :
    before = Znth 0 before 0 :: sublist 1 n before).
  { apply list_head_tail_by_sublist; lia. }
  assert (Hcur_cons :
    replace_Znth 0 (Znth (n - 1) before 0) before =
    Znth (n - 1) before 0 :: sublist 1 n before).
  {
    rewrite Hbefore_cons at 1 2 3.
    change (Znth 0 before 0 :: sublist 1 n before)
      with ((Znth 0 before 0 :: nil) ++ sublist 1 n before).
    rewrite replace_Znth_app_l
      with (l1 := (Znth 0 before 0 :: nil)) (l2 := sublist 1 n before).
    2:{ lia. }
    2:{
      change (Zlength (Znth 0 before 0 :: nil)) with 1.
      lia.
    }
    simpl.
    reflexivity.
  }
  unfold PopLoopState.
  split; [lia|].
  split; [exact Hlen|].
  split.
  - rewrite Zlength_replace_Znth.
    exact Hlen.
  - split; [lia|].
    split; [lia|].
    split.
    + exact HPQbefore_full.
    + split.
      { rewrite Hcur_cons.
        reflexivity. }
      split.
      { rewrite Znth_replace_Znth_Diff by lia.
        reflexivity. }
      split.
      { unfold PopRemainingElements.
        split; [lia|].
        split; [lia|].
        split.
        - rewrite Zlength_replace_Znth.
          lia.
        - rewrite Hcur_cons.
          replace (sublist 0 (n - 1) (Znth (n - 1) before 0 :: sublist 1 n before))
            with (Znth (n - 1) before 0 :: sublist 0 (n - 2) (sublist 1 n before)).
          2:{
            replace (n - 2) with ((n - 1) - 1) by lia.
            symmetry.
            apply sublist_cons1.
            lia.
          }
          assert (Hmid :
            sublist 0 (n - 2) (sublist 1 n before) = sublist 1 (n - 1) before).
          {
            rewrite Zsublist_Zsublist by lia.
            replace (0 + 1) with 1 by lia.
            replace (n - 2 + 1) with (n - 1) by lia.
            reflexivity.
          }
          replace
            (Znth (n - 1) before 0 :: sublist 0 (n - 2) (sublist 1 n before))
            with
            (Znth (n - 1) before 0 :: sublist 1 (n - 1) before).
          2:{ f_equal. exact (eq_sym Hmid). }
          rewrite (sublist_split 1 n (n - 1) before) by lia.
          replace (sublist (n - 1) n before) with (Znth (n - 1) before 0 :: nil).
          2:{
            replace (sublist (n - 1) n before)
              with (sublist (n - 1) ((n - 1) + 1) before) by (f_equal; lia).
            symmetry.
            apply sublist_single.
            lia.
          }
          simpl.
          apply Permutation_cons_append.
      }
      split.
      { unfold HeapOrderExceptDown.
        split; [lia|].
        split; [lia|].
        intros child [Hchild_pos [Hchild_lt Hparent_neq]].
        destruct (heap_parent_bounds_pos child Hchild_pos)
          as [Hparent0 Hparentlt].
        rewrite Znth_replace_Znth_Diff by lia.
        rewrite Znth_replace_Znth_Diff by lia.
        apply Hheap_ord.
        lia.
      }
      { unfold PopHoleParentDominatesChildren.
        left.
        reflexivity.
      }
Qed.

Lemma replace_Znth_last_as_app : forall (l : list Z) n v (d : Z),
  0 < n ->
  Zlength l = n ->
  replace_Znth (n - 1) v l = sublist 0 (n - 1) l ++ v :: nil.
Proof.
  intros l n v d Hn Hlen.
  replace l with (sublist 0 (n - 1) l ++ sublist (n - 1) n l).
  2:{
    rewrite <- (sublist_split 0 n (n - 1) l) by lia.
    apply sublist_self.
    lia.
  }
  rewrite replace_Znth_app_r by (rewrite Zlength_sublist; lia).
  rewrite replace_Znth_nothing by (rewrite Zlength_sublist; lia).
  rewrite Zlength_sublist by lia.
  replace (n - 1 - (n - 1)) with 0 by lia.
  replace (sublist (n - 1) n l) with (Znth (n - 1) l d :: nil).
  2:{
    replace (sublist (n - 1) n l)
      with (sublist (n - 1) ((n - 1) + 1) l) by (f_equal; lia).
    symmetry.
    apply sublist_single.
    lia.
  }
  replace (n - 1 - (n - 1 - 0)) with 0 by lia.
  simpl.
  rewrite sublist_split_app_l by (try rewrite Zlength_sublist; lia).
  rewrite (sublist_self (sublist 0 (n - 1) l) (n - 1)).
  2:{ rewrite Zlength_sublist; lia. }
  reflexivity.
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
    Permutation l (replace_Znth j (Znth i l d) (replace_Znth i (Znth j l d) l)).
Proof.
  intros l i j d Hrange.
  destruct Hrange as [Hi [Hij Hj]].
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
  assert (Hj_lr: (nj < List.length lr)%nat).
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
      rewrite Nat.add_comm.
      rewrite Hnat.
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
    Permutation l (replace_Znth j (Znth i l d) (replace_Znth i (Znth j l d) l)).
Proof.
  intros l i j d Hi Hj.
  destruct (Z_lt_ge_dec i j) as [Hij | Hge].
  - apply permutation_swap_Znth_lt.
    lia.
  - destruct (Z_lt_ge_dec j i) as [Hji | Heq].
    + rewrite replace_Znth_comm by lia.
      apply permutation_swap_Znth_lt.
      lia.
    + assert (i = j) by lia.
      subst j.
      rewrite replace_Znth_Znth by lia.
      rewrite replace_Znth_Znth by lia.
      apply Permutation_refl.
Qed.

Lemma sublist_prefix_swap :
  forall cur size i j (d : Z),
    0 <= i < size ->
    0 <= j < size ->
    size <= Zlength cur ->
    sublist 0 size
      (replace_Znth j (Znth i cur d) (replace_Znth i (Znth j cur d) cur)) =
    replace_Znth j (Znth i cur d)
      (replace_Znth i (Znth j cur d) (sublist 0 size cur)).
Proof.
  intros cur size i j d Hi Hj Hsize.
  set (prefix := sublist 0 size cur).
  set (suffix := sublist size (Zlength cur) cur).
  assert (Hsplit : cur = prefix ++ suffix).
  {
    subst prefix suffix.
    rewrite <- (sublist_split 0 (Zlength cur) size cur) by lia.
    symmetry.
    apply sublist_self.
    reflexivity.
  }
  assert (Hinner :
    replace_Znth i (Znth j cur d) cur =
    replace_Znth i (Znth j cur d) prefix ++ suffix).
  {
    rewrite Hsplit.
    rewrite replace_Znth_app_l with (l1 := prefix) (l2 := suffix).
    2:{ lia. }
    2:{ subst prefix. rewrite Zlength_sublist by lia. lia. }
    reflexivity.
  }
  assert (Hwhole :
    replace_Znth j (Znth i cur d) (replace_Znth i (Znth j cur d) cur) =
    replace_Znth j (Znth i cur d)
      (replace_Znth i (Znth j cur d) prefix) ++ suffix).
  {
    rewrite Hinner.
    rewrite replace_Znth_app_l
      with (l1 := replace_Znth i (Znth j cur d) prefix) (l2 := suffix).
    2:{ lia. }
    2:{ rewrite Zlength_replace_Znth. subst prefix. rewrite Zlength_sublist by lia. lia. }
    reflexivity.
  }
  rewrite Hwhole.
  replace size with
    (Zlength
      (replace_Znth j (Znth i cur d) (replace_Znth i (Znth j cur d) prefix))).
  2:{ rewrite !Zlength_replace_Znth. subst prefix. rewrite Zlength_sublist by lia. lia. }
  apply sublist_app_exact1.
Qed.

Lemma pop_loop_swap_down_preserve : forall before cur n idx largest,
  PopLoopState before cur n idx ->
  PopSelectedChild cur (n - 1) idx largest ->
  Znth idx cur 0 < Znth largest cur 0 ->
  let cur2 :=
    replace_Znth largest (Znth idx cur 0)
      (replace_Znth idx (Znth largest cur 0) cur) in
  idx < largest /\ PopLoopState before cur2 n largest.
Proof.
  intros before cur n idx largest Hstate Hsel Hlt.
  destruct Hsel as
    [_ [_ [Hidx_largest [Hlargest0 [Hlargestlt [Hlargest_parent Hlargest_dom]]]]]].
  destruct Hstate as
    [Hn [Hbefore [Hcur [Hidx0 [Hidxlt [HPQbefore [Hidxval [Hlast [Hremain [Hexcept Hparentdom]]]]]]]]]].
  destruct Hexcept as [Hexcept0 [Hexcept_bound Hexcept_ord]].
  set (cur2 :=
    replace_Znth largest (Znth idx cur 0)
      (replace_Znth idx (Znth largest cur 0) cur)).
  assert (Hidx_range : 0 <= idx < Zlength cur) by (rewrite Hcur; lia).
  assert (Hlargest_range : 0 <= largest < Zlength cur) by (rewrite Hcur; lia).
  assert (Hswap_idx :
    Znth idx cur2 0 = Znth largest cur 0).
  {
    unfold cur2.
    rewrite Znth_replace_Znth_Diff by (repeat rewrite Zlength_replace_Znth; lia).
    rewrite Znth_replace_Znth_Same by lia.
    reflexivity.
  }
  assert (Hswap_largest :
    Znth largest cur2 0 = Znth idx cur 0).
  {
    unfold cur2.
    rewrite Znth_replace_Znth_Same by (repeat rewrite Zlength_replace_Znth; lia).
    reflexivity.
  }
  assert (Hswap_other :
    forall k,
      0 <= k < Zlength cur ->
      k <> idx ->
      k <> largest ->
      Znth k cur2 0 = Znth k cur 0).
  {
    intros k Hk Hk_idx Hk_largest.
    unfold cur2.
    rewrite Znth_replace_Znth_Diff by (repeat rewrite Zlength_replace_Znth; lia).
    rewrite Znth_replace_Znth_Diff by lia.
    reflexivity.
  }
  split; [exact Hidx_largest|].
  unfold PopLoopState.
  split; [exact Hn|].
  split; [exact Hbefore|].
  split.
  - unfold cur2.
    repeat rewrite Zlength_replace_Znth.
    exact Hcur.
  - split; [exact Hlargest0|].
    split; [exact Hlargestlt|].
    split; [exact HPQbefore|].
    split.
    + rewrite Hswap_largest.
      exact Hidxval.
    + split.
      * assert (Hlast_range : 0 <= n - 1 < Zlength cur) by (rewrite Hcur; lia).
        rewrite (Hswap_other (n - 1) Hlast_range) by lia.
        exact Hlast.
      * split.
        { destruct Hremain as [Hn1 [Hbefore_bound [Hcur_bound Hperm_remain]]].
          unfold PopRemainingElements.
          split; [exact Hn1|].
          split; [exact Hbefore_bound|].
          split.
          - unfold cur2.
            repeat rewrite Zlength_replace_Znth.
            exact Hcur_bound.
          - assert (Hprefix_swap :
              sublist 0 (n - 1) cur2 =
              replace_Znth largest (Znth idx (sublist 0 (n - 1) cur) 0)
                (replace_Znth idx (Znth largest (sublist 0 (n - 1) cur) 0)
                  (sublist 0 (n - 1) cur))).
            {
              unfold cur2.
              rewrite sublist_prefix_swap by (try lia; rewrite Hcur; lia).
              rewrite Znth_sublist0 by lia.
              rewrite Znth_sublist0 by lia.
              reflexivity.
            }
            assert (Hsublen : Zlength (sublist 0 (n - 1) cur) = n - 1).
            {
              rewrite Zlength_sublist by lia.
              lia.
            }
            rewrite Hprefix_swap.
            eapply Permutation_trans with (l' := sublist 0 (n - 1) cur).
            { apply Permutation_sym.
              apply permutation_swap_Znth;
              rewrite Hsublen;
              lia. }
            exact Hperm_remain.
        }
        split.
        { unfold HeapOrderExceptDown.
          split; [exact Hlargest0|].
          split; [exact Hlargestlt|].
          intros child [Hchild_pos [Hchild_lt Hparent_neq_largest]].
          destruct (Z.eq_dec child largest) as [Hchild_largest | Hchild_not_largest].
          - subst child.
            rewrite Hlargest_parent.
            rewrite Hswap_idx, Hswap_largest.
            lia.
          - destruct (Z.eq_dec child idx) as [Hchild_idx | Hchild_not_idx].
            + subst child.
              destruct Hparentdom as [Hidx_zero | Hparentdom'].
              * subst idx.
                lia.
              * assert (Hparent_dom_large :
                  Znth (HeapParent idx) cur 0 >= Znth largest cur 0).
                {
                  apply Hparentdom'.
                  split; [lia|].
                  split; [exact Hlargestlt|].
                  exact Hlargest_parent.
                }
                assert (Hparent_idx_bounds : 0 <= HeapParent idx < idx).
                {
                  apply heap_parent_bounds_pos.
                  lia.
                }
                destruct Hparent_idx_bounds as [Hparent_idx0 Hparent_idx_lt].
                assert (Hparent_idx_range : 0 <= HeapParent idx < Zlength cur) by
                  (rewrite Hcur; lia).
                rewrite (Hswap_other (HeapParent idx) Hparent_idx_range) by lia.
                rewrite Hswap_idx.
                exact Hparent_dom_large.
            + destruct (Z.eq_dec (HeapParent child) idx) as [Hparent_idx | Hparent_not_idx].
              * rewrite Hparent_idx.
                rewrite Hswap_idx.
                assert (Hchild_range : 0 <= child < Zlength cur) by (rewrite Hcur; lia).
                rewrite (Hswap_other child Hchild_range Hchild_not_idx Hchild_not_largest).
                apply Hlargest_dom.
                split; [exact Hchild_pos|].
                split; [exact Hchild_lt|].
                exact Hparent_idx.
              * assert (Hparent_range : 0 <= HeapParent child < Zlength cur).
                {
                  destruct (heap_parent_bounds_pos child Hchild_pos) as [Hparent0 Hparentlt].
                  rewrite Hcur; lia.
                }
                assert (Hchild_range : 0 <= child < Zlength cur) by (rewrite Hcur; lia).
                rewrite (Hswap_other (HeapParent child) Hparent_range Hparent_not_idx Hparent_neq_largest).
                rewrite (Hswap_other child Hchild_range Hchild_not_idx Hchild_not_largest).
                apply Hexcept_ord.
                split; [exact Hchild_pos|].
                split; [exact Hchild_lt|].
                exact Hparent_not_idx.
        }
        { unfold PopHoleParentDominatesChildren.
          right.
          intros child [Hchild_pos [Hchild_lt Hchild_parent]].
          rewrite Hlargest_parent.
          rewrite Hswap_idx.
          assert (Hchild_range : 0 <= child < Zlength cur) by (rewrite Hcur; lia).
          assert (Hchild_not_idx : child <> idx).
          {
            intro Heq.
            subst child.
            assert (Hidx_pos : 0 < idx) by lia.
            destruct (heap_parent_bounds_pos idx Hidx_pos) as [_ Hparentlt].
            rewrite Hchild_parent in Hparentlt.
            lia.
          }
          assert (Hchild_not_largest : child <> largest).
          {
            intro Heq.
            subst child.
            rewrite Hlargest_parent in Hchild_parent.
            lia.
          }
          rewrite (Hswap_other child Hchild_range Hchild_not_idx Hchild_not_largest).
          rewrite <- Hchild_parent.
          apply Hexcept_ord.
          split; [exact Hchild_pos|].
          split; [exact Hchild_lt|].
          rewrite Hchild_parent.
          lia.
        }
Qed.

Lemma priority_queue_prefix_replace_at_end : forall cur size v,
  0 <= size ->
  size < Zlength cur ->
  PriorityQueuePrefix cur size ->
  PriorityQueuePrefix (replace_Znth size v cur) size.
Proof.
  intros cur size v Hsize Hbound [Hheap Hmax].
  assert (Hsame: forall i,
    0 <= i < size ->
    Znth i (replace_Znth size v cur) 0 = Znth i cur 0).
  {
    intros i Hi.
    rewrite Znth_replace_Znth_Diff; lia.
  }
  split.
  - unfold MaxHeapPrefix in *.
    destruct Hheap as [Hheap0 [Hheaplen Hheapord]].
    split; [lia|].
    split; [rewrite Zlength_replace_Znth; lia|].
    intros child [Hchildpos Hchildlt].
    destruct (heap_parent_bounds_pos child Hchildpos) as [Hparent0 Hparentlt].
    rewrite Hsame by lia.
    rewrite Hsame by lia.
    apply Hheapord.
    lia.
  - intros Hnonempty.
    specialize (Hmax Hnonempty).
    unfold PrefixMaxValue in *.
    destruct Hmax as [Hprefix_pos [Hprefix_len [a [[Ha Hdom] Hval]]]].
    destruct Ha as [Ha0 Ha1].
    split; [lia|].
    split; [rewrite Zlength_replace_Znth; lia|].
    exists a.
    split.
    + split.
      * split; lia.
      * intros b Hb.
        destruct Hb as [Hb0 Hb1].
        rewrite Hsame by lia.
        rewrite Hsame by lia.
        apply Hdom.
        split; lia.
    + rewrite Hsame by lia.
      rewrite Hsame by lia.
      exact Hval.
Qed.

Lemma pop_remaining_replace_last_permutation : forall before cur n ret,
  ret = Znth 0 before 0 ->
  Zlength before = n ->
  Zlength cur = n ->
  PopRemainingElements before cur n ->
  Permutation before (replace_Znth (n - 1) ret cur).
Proof.
  intros before cur n ret Hret Hbefore Hcur Hremain.
  destruct Hremain as [Hn1 [Hbefore_bound [Hcur_bound Hperm]]].
  rewrite (list_head_tail_by_sublist before n 0) by lia.
  rewrite (replace_Znth_last_as_app cur n ret 0) by lia.
  rewrite <- Hret.
  eapply Permutation_trans.
  - apply Permutation_cons_append.
  - apply Permutation_app_tail.
    symmetry.
    exact Hperm.
Qed.

Lemma pop_ready_final_write_to_result_with_range : forall before cur n ret,
  PopReadyState before cur n ret ->
  -2147483648 <= ret ->
  ret <= 2147483647 ->
  (forall pos, 0 <= pos < n ->
    -2147483648 <= Znth pos cur 0 <= 2147483647) ->
  PopResult before (replace_Znth (n - 1) ret cur) n ret /\
  (forall pos, 0 <= pos < n ->
    -2147483648 <= Znth pos (replace_Znth (n - 1) ret cur) 0 <= 2147483647).
Proof.
  intros before cur n ret Hready Hret_low Hret_high Hrange.
  destruct Hready as
    [Hn [Hbefore [Hcur [HPQbefore [Hprefix [Hret [Hlast [Hremain HPQcur]]]]]]]].
  split.
  - unfold PopResult.
    split; [lia|].
    split; [exact Hbefore|].
    split; [rewrite Zlength_replace_Znth; exact Hcur|].
    split; [exact HPQbefore|].
    split; [exact Hprefix|].
    split; [exact Hret|].
    split; [rewrite Znth_replace_Znth_Same by lia; reflexivity|].
    split.
    + apply priority_queue_prefix_replace_at_end; try lia.
      exact HPQcur.
    + apply pop_remaining_replace_last_permutation; try assumption.
  - intros pos Hpos.
    destruct (Z.eq_dec pos (n - 1)) as [Heq | Hneq].
    + subst pos.
      rewrite Znth_replace_Znth_Same by lia.
      split; assumption.
    + rewrite Znth_replace_Znth_Diff by lia.
      apply Hrange.
      exact Hpos.
Qed.
