(* SllPtrArrayLib: reusable separation-logic shape for a flat array of
   (singly-linked) list head pointers, i.e. `struct list *arr[n]`.

   This is the sll-row analogue of [SeparationLogic/SeparationLogic/PtrArray2LibCore.v],
   whose functor assumes each row is an [ElemArray] (a flat array of elements).
   An sll row is a *variable-length* linked list, not an [ElemArray], so it
   cannot go through the functor; this file hand-writes the same structure with
   the single row-coupling point replaced:

     PtrArray2LibCore.row_block pr := ElemArray.full (fst pr) (Zlength (snd pr)) (snd pr)
     SllPtrArrayLib.sll_row_block pr := sll (fst pr) (snd pr)

   Everything else (flat [PtrArray] for the pointer spine, [missing_i] shape,
   the generic [iter_sepcon_split_remove_Znth] / [iter_sepcon_merge_remove_Znth]
   decomposition lemmas) is reused verbatim from the functor core.

   Pure shape library: the predicates below are memory-shape mappings
   (pointer-array spine ** one sll per row), not an algorithm mirror. *)
Require Import Coq.Strings.String.
Require Import Coq.Init.Datatypes.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap ListLib.
From compcert.lib Require Import Integers.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic CommonAssertion StoreAux ArrayLib.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Import ListNotations.
Local Open Scope list.

Import naive_C_Rules.
Local Open Scope sac.

Require Import SimpleC.EE.QCP_demos_LLM.sll_lib.

(* ------------------------------------------------------------------ *)
(* Generic list helpers (copied verbatim from PtrArray2LibCore, so     *)
(* that this nonfunctor file is self-contained: they do not depend on  *)
(* the row type).                                                      *)
(* ------------------------------------------------------------------ *)

Definition remove_Znth {B : Type} (i : Z) (l : list B) : list B :=
  firstn (Z.to_nat i) l ++ skipn (S (Z.to_nat i)) l.

Lemma replace_nth_decomp : forall {B : Type} n (l : list B) (v : B),
  (n < length l)%nat ->
  replace_nth n l v = firstn n l ++ v :: skipn (S n) l.
Proof.
  intros.
  revert n H; induction l; intros; simpl in *; try lia.
  destruct n; simpl.
  - reflexivity.
  - f_equal.
    apply IHl.
    lia.
Qed.

Lemma replace_Znth_decomp : forall {B : Type} i (l : list B) (v : B),
  0 <= i < Zlength l ->
  replace_Znth i v l = firstn (Z.to_nat i) l ++ v :: skipn (S (Z.to_nat i)) l.
Proof.
  intros.
  unfold replace_Znth.
  apply replace_nth_decomp.
  rewrite Zlength_correct in H.
  apply Nat2Z.inj_lt.
  rewrite Z2Nat.id by lia.
  lia.
Qed.

Lemma Znth_combine : forall {B C : Type} i (l1 : list B) (l2 : list C) d1 d2,
  0 <= i < Zlength l1 ->
  Zlength l1 = Zlength l2 ->
  Znth i (combine l1 l2) (d1, d2) = (Znth i l1 d1, Znth i l2 d2).
Proof.
  intros B C i l1.
  revert i; induction l1 as [|b l1 IHl1]; intros.
  - rewrite Zlength_correct in H. simpl in H. lia.
  - destruct l2 as [|c l2].
    + rewrite !Zlength_correct in H0. simpl in H0. lia.
    + simpl.
      destruct (Z_le_lt_eq_dec 0 i ltac:(lia)) as [Hi | Hi].
      * rewrite (Znth_cons (d1, d2) i (b, c) (combine l1 l2)) by lia.
        rewrite (Znth_cons d1 i b l1) by lia.
        rewrite (Znth_cons d2 i c l2) by lia.
        apply IHl1.
        -- rewrite Zlength_correct in *. simpl in *. lia.
        -- rewrite !Zlength_correct in *. simpl in *. lia.
      * subst i.
        rewrite (Znth0_cons (d1, d2) (b, c) (combine l1 l2)).
        rewrite (Znth0_cons d1 b l1).
        rewrite (Znth0_cons d2 c l2).
        reflexivity.
Qed.

Lemma combine_replace_Znth_r : forall {B C : Type} i (l1 : list B) (l2 : list C) d1 v,
  0 <= i < Zlength l1 ->
  Zlength l1 = Zlength l2 ->
  combine l1 (replace_Znth i v l2) =
  replace_Znth i (Znth i l1 d1, v) (combine l1 l2).
Proof.
  intros B C i l1.
  revert i; induction l1 as [|b l1 IHl1]; intros.
  - rewrite Zlength_correct in H. simpl in H. lia.
  - destruct l2 as [|c l2].
    + rewrite !Zlength_correct in H0. simpl in H0. lia.
    + simpl.
      destruct (Z_le_lt_eq_dec 0 i ltac:(lia)) as [Hi | Hi].
      * rewrite replace_Znth_cons by lia.
        rewrite replace_Znth_cons by lia.
        rewrite (Znth_cons d1 i b l1) by lia.
        f_equal.
        apply IHl1.
        -- rewrite Zlength_correct in *. simpl in *. lia.
        -- rewrite !Zlength_correct in *. simpl in *. lia.
      * subst i.
        reflexivity.
Qed.

Lemma single_to_iter_sepcon : forall P : Assertion,
  P |-- iter_sepcon [P].
Proof.
  intros.
  simpl.
  eapply derivable1_trans.
  - apply derivable1_sepcon_emp_r.
  - apply derivable1_sepcon_comm.
Qed.

Lemma iter_sepcon_split_remove_Znth : forall {B : Type} (P : B -> Assertion) i (l : list B) d,
  0 <= i < Zlength l ->
  iter_sepcon (map P l) |--
    P (Znth i l d) ** iter_sepcon (map P (remove_Znth i l)).
Proof.
  intros.
  unfold remove_Znth.
  rewrite (firstn_skipSn d (Z.to_nat i) l) at 1 by (rewrite Zlength_correct in H; lia).
  unfold Znth.
  rewrite !map_app.
  change (map P (firstn (Z.to_nat i) l) ++
          P (nth (Z.to_nat i) l d) :: map P (skipn (S (Z.to_nat i)) l))
    with (map P (firstn (Z.to_nat i) l) ++
          [P (nth (Z.to_nat i) l d)] ++ map P (skipn (S (Z.to_nat i)) l)).
  rewrite derivable1_sepcon_iter_sepcon2.
  sep_apply (derivable1_sepcon_iter_sepcon2
    [P (nth (Z.to_nat i) l d)]
    (map P (skipn (S (Z.to_nat i)) l))).
  rewrite derivable1_iter_sepcon_l.
  simpl.
  rewrite <- derivable1_sepcon_iter_sepcon1.
  entailer!.
  all: entailer!.
  rewrite derivable1_iter_sepcon_l.
  simpl.
  entailer!.
  Unshelve.
  all: try (rewrite Zlength_combine_eq by auto); try lia.
Qed.

Lemma iter_sepcon_merge_remove_Znth : forall {B : Type} (P : B -> Assertion) i (l : list B) v,
  0 <= i < Zlength l ->
  P v ** iter_sepcon (map P (remove_Znth i l)) |--
    iter_sepcon (map P (replace_Znth i v l)).
Proof.
  intros.
  unfold remove_Znth.
  rewrite (replace_Znth_decomp i l v) by lia.
  rewrite !map_app.
  change (map P (firstn (Z.to_nat i) l) ++
          P v :: map P (skipn (S (Z.to_nat i)) l))
    with (map P (firstn (Z.to_nat i) l) ++
          [P v] ++ map P (skipn (S (Z.to_nat i)) l)).
  sep_apply (derivable1_sepcon_iter_sepcon2
    (map P (firstn (Z.to_nat i) l))
    (map P (skipn (S (Z.to_nat i)) l))).
  sep_apply (derivable1_sepcon_comm
    (iter_sepcon (map P (skipn (S (Z.to_nat i)) l)))
    (P v)).
  rewrite derivable1_sepcon_assoc1.
  sep_apply (single_to_iter_sepcon (P v)).
  sep_apply (derivable1_sepcon_iter_sepcon1
    [P v]
    (map P (skipn (S (Z.to_nat i)) l))).
  rewrite derivable1_sepcon_comm.
  sep_apply (derivable1_sepcon_iter_sepcon1
    (map P (firstn (Z.to_nat i) l))
    ([P v] ++ map P (skipn (S (Z.to_nat i)) l))).
  entailer!.
  all: entailer!.
Qed.

Lemma Zlength_combine_eq : forall {B C : Type} (l1 : list B) (l2 : list C),
  Zlength l1 = Zlength l2 ->
  Zlength (combine l1 l2) = Zlength l1.
Proof.
  intros.
  rewrite !Zlength_correct in *.
  apply Nat2Z.inj in H.
  rewrite length_combine.
  rewrite <- H.
  replace (Init.Nat.min (length l1) (length l1)) with (length l1) by lia.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* The single coupling point: each row is an sll (variable-length      *)
(* singly-linked list of Z), not an ElemArray.                         *)
(* ------------------------------------------------------------------ *)

Definition sll_row_block (pr : addr * list Z) : Assertion :=
  sll (fst pr) (snd pr).

Definition sll_row_blocks (row_ptrs : list Z) (rows : list (list Z)) : Assertion :=
  iter_sepcon (map sll_row_block (combine row_ptrs rows)).

Definition sll_row_blocks_missing_i
  (i : Z) (row_ptrs : list Z) (rows : list (list Z)) : Assertion :=
  iter_sepcon (map sll_row_block (remove_Znth i (combine row_ptrs rows))).

(* Flat pointer-array spine + one sll per row. *)
Module SllPtrArray.

Definition full (x : addr) (n : Z) (rows : list (list Z)) : Assertion :=
  EX row_ptrs : list Z,
    “ Zlength row_ptrs = n /\ Zlength rows = n ” &&
    PtrArray.full x n row_ptrs **
    sll_row_blocks row_ptrs rows.

Definition missing_i
  (x : addr) (n i row_ptr : Z) (rows : list (list Z)) : Assertion :=
  EX row_ptrs : list Z,
    “ Zlength row_ptrs = n /\ Zlength rows = n /\ row_ptr = Znth i row_ptrs 0 ” &&
    PtrArray.missing_i x i 0 n row_ptrs **
    sll_row_blocks_missing_i i row_ptrs rows.

End SllPtrArray.

(* ------------------------------------------------------------------ *)
(* Auxiliary lemmas.                                                   *)
(* ------------------------------------------------------------------ *)

Lemma SllPtrArray_full_Zlength : forall x n rows,
  SllPtrArray.full x n rows |-- “ Zlength rows = n ”.
Proof.
  intros.
  unfold SllPtrArray.full.
  Intros row_ptrs.
  entailer!.
Qed.

Lemma sll_row_blocks_split_to_missing_i : forall i row_ptrs rows,
  0 <= i < Zlength row_ptrs ->
  Zlength row_ptrs = Zlength rows ->
  sll_row_blocks row_ptrs rows |--
    sll (Znth i row_ptrs 0) (Znth i rows nil) **
    sll_row_blocks_missing_i i row_ptrs rows.
Proof.
  intros.
  unfold sll_row_blocks, sll_row_blocks_missing_i, sll_row_block.
  assert (Hcombine : 0 <= i < Zlength (combine row_ptrs rows)).
  { rewrite Zlength_combine_eq by auto. lia. }
  sep_apply (iter_sepcon_split_remove_Znth
    sll_row_block i (combine row_ptrs rows) (0, nil) Hcombine).
  assert (HZnth:
    Znth i (combine row_ptrs rows) (0, nil) =
    (Znth i row_ptrs 0, Znth i rows nil)).
  { apply Znth_combine; auto. }
  assert (Hrow:
    sll_row_block (Znth i (combine row_ptrs rows) (0, nil)) |--
    sll (Znth i row_ptrs 0) (Znth i rows nil)).
  { rewrite HZnth. unfold sll_row_block. simpl. entailer!. }
  sep_apply Hrow.
  entailer!.
Qed.

(* Merge a fresh sll row back into the i-th slot. Unlike IntArray rows, an sll
   row carries its own length, so no length argument is needed here. *)
Lemma sll_row_blocks_missing_i_merge_to_full : forall i row_ptrs rows row,
  0 <= i < Zlength row_ptrs ->
  Zlength row_ptrs = Zlength rows ->
  sll (Znth i row_ptrs 0) row **
  sll_row_blocks_missing_i i row_ptrs rows |--
    sll_row_blocks row_ptrs (replace_Znth i row rows).
Proof.
  intros.
  unfold sll_row_blocks, sll_row_blocks_missing_i, sll_row_block.
  assert (Hcombine : 0 <= i < Zlength (combine row_ptrs rows)).
  { rewrite Zlength_combine_eq by auto. lia. }
  replace (combine row_ptrs (replace_Znth i row rows))
    with (replace_Znth i (Znth i row_ptrs 0, row) (combine row_ptrs rows)).
  2: { symmetry. apply combine_replace_Znth_r; auto. }
  sep_apply (iter_sepcon_merge_remove_Znth
    sll_row_block i (combine row_ptrs rows) (Znth i row_ptrs 0, row) Hcombine).
  simpl.
  entailer!.
Qed.

(* The two strategy-driver lemmas, mirroring IntPtrArray2.full_split_to_missing_i
   and IntPtrArray2.missing_i_merge_to_full but with an sll row in place of
   IntArray.full. *)
Lemma SllPtrArray_full_split_to_missing_i : forall x i n rows,
  0 <= i < n ->
  SllPtrArray.full x n rows |--
    EX row_ptr,
      StorePtrAsElement.storeA x i row_ptr **
      sll row_ptr (Znth i rows nil) **
      SllPtrArray.missing_i x n i row_ptr rows.
Proof.
  intros.
  unfold SllPtrArray.full, SllPtrArray.missing_i.
  Intros row_ptrs.
  destruct H0 as [Hrow_ptrs Hrows].
  Exists (Znth i row_ptrs 0).
  Exists row_ptrs.
  entailer!.
  assert (Hi_ptrs : 0 <= i < Zlength row_ptrs) by lia.
  assert (Hlen_rows : Zlength row_ptrs = Zlength rows) by lia.
  sep_apply (PtrArray.full_split_to_missing_i x i n row_ptrs 0 H).
  sep_apply (sll_row_blocks_split_to_missing_i i row_ptrs rows Hi_ptrs Hlen_rows).
  entailer!.
Qed.

Lemma SllPtrArray_missing_i_merge_to_full : forall x i n row_ptr rows row,
  0 <= i < n ->
  StorePtrAsElement.storeA x i row_ptr **
  sll row_ptr row **
  SllPtrArray.missing_i x n i row_ptr rows |--
    SllPtrArray.full x n (replace_Znth i row rows).
Proof.
  intros.
  unfold SllPtrArray.missing_i, SllPtrArray.full.
  Intros row_ptrs.
  destruct H0 as [Hrow_ptrs [Hrows Hrow_ptr]].
  subst row_ptr.
  Exists row_ptrs.
  entailer!.
  - assert (Hi_ptrs : 0 <= i < Zlength row_ptrs) by lia.
    assert (Hlen_rows : Zlength row_ptrs = Zlength rows) by lia.
    eapply derivable1_trans with
      (y := (StorePtrAsElement.storeA x i (Znth i row_ptrs 0) **
             PtrArray.missing_i x i 0 n row_ptrs) **
            (sll (Znth i row_ptrs 0) row **
             sll_row_blocks_missing_i i row_ptrs rows)).
    + entailer!.
    + unfold StorePtrAsElement.storeA at 1.
      sep_apply (PtrArray.missing_i_merge_to_full
        x i n (Znth i row_ptrs 0) row_ptrs H).
      rewrite replace_Znth_Znth by auto.
      sep_apply (sll_row_blocks_missing_i_merge_to_full
        i row_ptrs rows row Hi_ptrs Hlen_rows).
      entailer!.
  - rewrite Zlength_replace_Znth.
    auto.
Qed.
