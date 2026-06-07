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
From SimpleC.EE.Applications_human.LiteOS Require Import GetSortLinkNextExpireTime_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.Applications_human.LiteOS.lib.glob_vars_and_defs.
Require Import SimpleC.EE.Applications_human.LiteOS.lib.sortlink.
Require Import SimpleC.EE.Applications_human.LiteOS.lib.dll.
Require Import SimpleC.EE.Applications_human.LiteOS.lib.tick_backup.
Local Open Scope sac.

Lemma dllseg_head_insert:
  forall (A: Type) (storeA: Z -> A -> Assertion) 
         (py y z x pt: Z) (a: A) (l: list (DL_Node A)),
    dllseg storeA z y x pt l **
    storeA y a **
    &(y # "LOS_DL_LIST" ->ₛ "pstPrev") # Ptr |-> py **
    &(y # "LOS_DL_LIST" ->ₛ "pstNext") # Ptr |-> z |--
    dllseg storeA y py x pt ((Build_DL_Node a y) :: l).
Proof.
    intros.
    simpl.
    Exists z.
    entailer!.
Qed.


Lemma dllseg_head_split:
  forall (A: Type) (storeA: Z -> A -> Assertion) 
         (y py x pt: Z) (a: A) (l: list (DL_Node A)),
    dllseg storeA y py x pt ((Build_DL_Node a y) :: l) |--
    EX z,
    dllseg storeA z y x pt l **
    storeA y a **
    &(y # "LOS_DL_LIST" ->ₛ "pstPrev") # Ptr |-> py **
    &(y # "LOS_DL_LIST" ->ₛ "pstNext") # Ptr |-> z.
Proof.
    intros.
    simpl.
    Intros z.
    Exists z.
    entailer!.
Qed.

Lemma head_trans:
forall (A: Type) (storeA: Z -> A -> Assertion) 
    (y py x pt az: Z) (a: A) (l: list (DL_Node A)),
  dllseg storeA y py x pt ((Build_DL_Node a az) :: l) |--
“ az = y ”.
Proof.
    intros.
    simpl.
    unfold store_dll.
    Intros z.
    rewrite H.
    entailer!.
Qed.

Lemma storesortedLinkNode_split : 
    forall (A : Type) (storeA : Z -> A -> Assertion) (y y0 : Z) (a : A) (t : Z),
    y = &( y0 # "SortLinkList" ->ₛ "sortLinkNode") ->
    storeA y (sl_data {| sl_data := a; responseTime := t |}) **
    &( y0 # "SortLinkList" ->ₛ "responseTime") # UInt64 |-> responseTime {| sl_data := a; responseTime := t |}|--
    storesortedLinkNode storeA y {| sl_data := a; responseTime := t |}.
Proof.
    intros.
    simpl.
    unfold storesortedLinkNode.
    Exists y0.
    entailer!.
Qed.

Lemma store_dll_shift_rev_unfold:
forall {A: Type} (storeA: addr -> A -> Assertion)(x: addr) (l: list (DL_Node A)),
  store_dll storeA x l |--
  EX xn: addr ,
  &(x # "LOS_DL_LIST" ->ₛ "pstNext") # Ptr |-> xn **
  &(xn # "LOS_DL_LIST" ->ₛ "pstPrev") # Ptr |-> x **
  dllseg_shift_rev storeA xn x l.
Proof.
  intros.
  unfold store_dll.
  Intros h pt.
  sep_apply (dllseg_to_dllseg_shift_rev storeA h x x pt l).
  Exists h.
  entailer!.
Qed.

Lemma map_sortedLinkNodeMapping_not_nil : forall [A B : Type]  (f : A -> B) (l : list A),
  map f l <> nil -> l <> nil.
Proof.
    pre_process.
    intros.
    csimpl.
    destruct l.
    +
    contradiction.
    +
    congruence.
Qed.

Lemma map_sortedLinkNodeMapping : forall [A: Type](d a: DL_Node (sortedLinkNode A)) (l1 l: list (DL_Node (sortedLinkNode A))),
  map sortedLinkNodeMapping (d::l) = a::l1 ->  d.(dll_data) = a.(dll_data).
Proof.
    pre_process.
    intros.
    csimpl.
    simpl in H.
    destruct d.
    destruct a.
    simpl in H.
    unfold sortedLinkNodeMapping in H.
    simpl in H.
    inversion H.
    simpl.
    reflexivity.
Qed.

Lemma proof_of_GetSortLinkNextExpireTime_entail_wit_1 : GetSortLinkNextExpireTime_entail_wit_1.
Proof. 
    unfold GetSortLinkNextExpireTime_entail_wit_1.
    pre_process.
    intros.
    Intros.
    destruct l.
    +
    unfold obtian_first_pointer.
    simpl.
    entailer!.
    destruct H as [Hh _].
    rewrite Hh.
    entailer!.
    +
    unfold obtian_first_pointer.
    simpl.
    Intros z.
    Exists z.
    entailer!.
    rewrite H.
    entailer!.
Qed. 


Lemma proof_of_GetSortLinkNextExpireTime_return_wit_3 : GetSortLinkNextExpireTime_return_wit_3.
Proof. 
    pre_process.
    intros.
    unfold store_sorted_dll.
    entailer!.
    unfold getFirstNodeExpireTime.
    destruct l.
    +
    unfold MaxTime.
    pose proof (unsigned_last_nbits_eq (ULLONG_MAX - tickPrecision_pre) 64).
    assert (0 <= ULLONG_MAX - tickPrecision_pre).
    lia. 
    assert ( ULLONG_MAX - tickPrecision_pre < 2 ^ 64).
    lia.
    lia.
    +
    simpl in PreH1.
    discriminate PreH1.
Qed. 

Lemma proof_of_GetSortLinkNextExpireTime_return_wit_2 : GetSortLinkNextExpireTime_return_wit_2.
Proof. 
    pre_process.
    intros.
    unfold store_sorted_dll.
    entailer!.
    pose proof storesortedLinkNode_split A storeA (&( retval_2 # "SortLinkList" ->ₛ "sortLinkNode")) retval_2 (sl_data a.(dll_data)) (responseTime a.(dll_data)) as HsplitNode. 
    sep_apply HsplitNode ; try auto.
    unfold store_dll.
    Exists &( retval_2 # "SortLinkList" ->ₛ "sortLinkNode") pt.
    simpl.
    pose proof dllseg_head_insert (sortedLinkNode A) (storesortedLinkNode storeA) (&( sortHead_pre # "SortLinkAttribute" ->ₛ "sortLink")) (&( retval_2 # "SortLinkList" ->ₛ "sortLinkNode")) pl (&( sortHead_pre # "SortLinkAttribute" ->ₛ "sortLink")) pt (mksortedLinkNode (sl_data a.(dll_data)) (responseTime a.(dll_data)))  l1 as HinsertNode. 
    simpl.
    entailer!.
    - revert HinsertNode.
      csimpl.
      intros.
      sep_apply HinsertNode.
      unfold obtian_first_pointer in PreH2.
      simpl in PreH2.
      simpl in PreH5.
      rewrite PreH5 in PreH2.
      rewrite PreH5.
      entailer!.
      try rewrite PreH2.
      entailer!.
    - unfold getFirstNodeExpireTime.
      pose proof map_sortedLinkNodeMapping_not_nil sortedLinkNodeMapping l.
      assert (l <> nil) ; auto.
      destruct l.
      + contradiction.
      + unfold getNodeExpireTime.
        pose proof (map_sortedLinkNodeMapping d a l1 l PreH5) as HmapDataEq.
        assert (unsigned_last_nbits (startTime_pre + tickPrecision_pre) 64 = startTime_pre + tickPrecision_pre) as Hunsigned.
        {
          pose proof (unsigned_last_nbits_eq (startTime_pre + tickPrecision_pre) 64).
          assert (0 <= startTime_pre + tickPrecision_pre) by lia.
          assert (startTime_pre + tickPrecision_pre < 2 ^ 64) by lia.
          lia.
        }
        rewrite Hunsigned in PreH1.
        rewrite Hunsigned.
        rewrite HmapDataEq.
        destruct (responseTime a.(dll_data) <=? startTime_pre + tickPrecision_pre)%Z eqn: En.
        * reflexivity.
        * apply Z.leb_gt in En; lia.
Qed.

Lemma proof_of_GetSortLinkNextExpireTime_return_wit_1 : GetSortLinkNextExpireTime_return_wit_1.
Proof.  
    pre_process.
    intros.
    csimpl.
    unfold store_sorted_dll.
    entailer!.
    pose proof storesortedLinkNode_split A storeA (&( retval_2 # "SortLinkList" ->ₛ "sortLinkNode")) retval_2 (sl_data a.(dll_data)) (responseTime a.(dll_data)) as HsplitNode. 
    sep_apply HsplitNode ; try auto.
    unfold store_dll.
    Exists &( retval_2 # "SortLinkList" ->ₛ "sortLinkNode") pt.
    csimpl.
    simpl.
    pose proof dllseg_head_insert (sortedLinkNode A) (storesortedLinkNode storeA) (&( sortHead_pre # "SortLinkAttribute" ->ₛ "sortLink")) (&( retval_2 # "SortLinkList" ->ₛ "sortLinkNode")) pl (&( sortHead_pre # "SortLinkAttribute" ->ₛ "sortLink")) pt (mksortedLinkNode (sl_data a.(dll_data)) (responseTime a.(dll_data)))  l1 as HinsertNode. 
    csimpl.
    simpl.
    entailer!.
    - revert HinsertNode.
      csimpl.
      intros.
      sep_apply HinsertNode.
      unfold obtian_first_pointer in PreH2.
      simpl in PreH2.
      simpl in PreH5.
      rewrite PreH5 in PreH2.
      rewrite PreH5.
      entailer!.
      try rewrite PreH2.
      entailer!.
    - unfold getFirstNodeExpireTime.
      pose proof map_sortedLinkNodeMapping_not_nil sortedLinkNodeMapping l.
      assert (l <> nil) ; try auto.
      destruct l.
      + contradiction.
      + unfold getNodeExpireTime.
        pose proof (map_sortedLinkNodeMapping d a l1 l PreH5) as HmapDataEq.
        assert (unsigned_last_nbits (startTime_pre + tickPrecision_pre) 64 = startTime_pre + tickPrecision_pre) as Hunsigned.
        {
          pose proof (unsigned_last_nbits_eq (startTime_pre + tickPrecision_pre) 64).
          assert (0 <= startTime_pre + tickPrecision_pre) by lia.
          assert (startTime_pre + tickPrecision_pre < 2 ^ 64) by lia.
          lia.
        }
        rewrite Hunsigned in PreH1.
        rewrite HmapDataEq.
        destruct (responseTime a.(dll_data) <=? startTime_pre + tickPrecision_pre)%Z eqn: En.
        * apply Z.leb_le in En; lia.
        * reflexivity.
Qed.

Lemma proof_of_GetSortLinkNextExpireTime_which_implies_wit_1 : GetSortLinkNextExpireTime_which_implies_wit_1.
Proof. 
    unfold GetSortLinkNextExpireTime_which_implies_wit_1.
    pre_process.
    intros.
    csimpl.
    unfold store_sorted_dll.
    unfold store_dll.
    Intros h pt.
    Exists pt h.
    csimpl.
    entailer!.
Qed. 


Lemma proof_of_GetSortLinkNextExpireTime_which_implies_wit_2 : GetSortLinkNextExpireTime_which_implies_wit_2.
Proof. 
    unfold GetSortLinkNextExpireTime_which_implies_wit_2.
    pre_process.
    intros.
    csimpl.
    unfold store_dll.
    Exists h pt.
    csimpl.
    entailer!.
Qed. 

Lemma proof_of_GetSortLinkNextExpireTime_which_implies_wit_3 : GetSortLinkNextExpireTime_which_implies_wit_3.
Proof. 
    unfold GetSortLinkNextExpireTime_which_implies_wit_3.
    pre_process.
    intros.
    unfold store_dll.
    Intros h pt.
    prop_apply (head_trans (sortedLinkNode A) (storesortedLinkNode storeA) h (&( sortHead # "SortLinkAttribute" ->ₛ "sortLink")) (&( sortHead # "SortLinkAttribute" ->ₛ "sortLink")) pt (&( listSorted # "SortLinkList" ->ₛ "sortLinkNode")) (mksortedLinkNode al t) l1).
    entailer!.
    rewrite H.
    pose proof dllseg_head_split (sortedLinkNode A) (storesortedLinkNode storeA) h (&( sortHead # "SortLinkAttribute" ->ₛ "sortLink")) (&( sortHead # "SortLinkAttribute" ->ₛ "sortLink")) pt (mksortedLinkNode al t) l1.
    sep_apply H0.
    Intros z.
    Exists pt z.
    simpl.
    entailer!.
    rewrite <- H.
    csimpl.
    entailer!.
Qed.

Lemma proof_of_GetSortLinkNextExpireTime_which_implies_wit_4 : GetSortLinkNextExpireTime_which_implies_wit_4.
Proof. 
    unfold GetSortLinkNextExpireTime_which_implies_wit_4.
    pre_process.
    intros.
    unfold storesortedLinkNode.
    csimpl.
    Intros y.
    apply addr_of_arrow_field_inv in H.
    rewrite H.
    entailer!.
Qed. 

Lemma proof_of_LOS_ListEmpty_derive_getfirstSpec_by_highSpec : LOS_ListEmpty_derive_getfirstSpec_by_highSpec.
Proof. 
    pre_process.
    Exists A storeA_getfirstSpec l_getfirstSpec.
    entailer!.
    rewrite <- derivable1_wand_sepcon_adjoint.
    entailer!.
    apply derivable1_orp_elim.
    - Intros retval_2.
    unfold store_dll.
    Intros h pt.
    unfold dllseg.
    destruct l_getfirstSpec.
    + entailer!.
    + Intros z.
    Right.
    Exists d l_getfirstSpec retval_2.
    Exists h pt.
    Exists z.
    entailer!.
    - Intros retval_2.
    Left.
    Exists retval_2.
    entailer!.
Qed.


Lemma proof_of_GetSortLinkNextExpireTime_partial_solve_wit_5_pure: GetSortLinkNextExpireTime_partial_solve_wit_5_pure.
Proof.
    pre_process.
    entailer!.
    unfold obtian_first_pointer.
    unfold obtian_first_pointer in PreH1.
    rewrite PreH4 in PreH1.
    exact PreH1.
Qed.
