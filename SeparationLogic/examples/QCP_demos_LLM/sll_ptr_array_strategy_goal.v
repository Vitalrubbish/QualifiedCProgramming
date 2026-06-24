Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.micromega.Psatz.
From SimpleC.SL Require Import SeparationLogic.
Import naive_C_Rules.
Require Import SimpleC.EE.QCP_demos_LLM.sll_lib.
Require Import SimpleC.EE.QCP_demos_LLM.SllPtrArrayLib.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope string.

Definition sll_ptr_array_strategy1 :=
  forall (i : Z) (n : Z) (__default_app1_Z : (@list Z)) (p : Z) (rows : (@list (@list Z))),
    TT &&
    (“ (Z.le 0 i) ”) &&
    (“ (Z.lt i n) ”) &&
    emp **
    ((SllPtrArray.full p n rows))
    |--
    EX (row_ptr : Z),
      (
      TT &&
      emp **
      ((SllPtrArray.missing_i p n i row_ptr rows)) **
      ((sll row_ptr (Znth i rows __default_app1_Z)))
      ) ** (
      ALL (v : Z),
        TT &&
        (“ (v = row_ptr) ”) &&
        emp -*
        TT &&
        emp **
        ((poly_store FET_ptr (Z.add p (Z.mul i (@sizeof_front_end_type FET_ptr))) v))
        ).

Definition sll_ptr_array_strategy4 :=
  forall (p : Z) (rows1 : (@list (@list Z))) (n : Z),
    TT &&
    emp **
    ((SllPtrArray.full p n rows1))
    |--
    (
    TT &&
    emp
    ) ** (
    ALL (rows2 : (@list (@list Z))),
      TT &&
      (“ (rows1 = rows2) ”) &&
      emp -*
      TT &&
      emp **
      ((SllPtrArray.full p n rows2))
      ).

Definition sll_ptr_array_strategy5 :=
  forall (p : Z) (i : Z) (rows : (@list (@list Z))) (row_ptr : Z) (n : Z),
    TT &&
    emp **
    ((SllPtrArray.missing_i p n i row_ptr rows))
    |--
    (
    TT &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((SllPtrArray.missing_i p n i row_ptr rows))
    ).

Definition sll_ptr_array_strategy2 :=
  forall (i : Z) (n : Z) (__default_app1_Z : (@list Z)) (rows : (@list (@list Z))) (row_ptr : Z) (p : Z),
    TT &&
    (“ (Z.le 0 i) ”) &&
    (“ (Z.lt i n) ”) &&
    emp **
    ((SllPtrArray.missing_i p n i row_ptr rows)) **
    ((sll row_ptr (Znth i rows __default_app1_Z))) **
    ((poly_store FET_ptr (Z.add p (Z.mul i (@sizeof_front_end_type FET_ptr))) row_ptr))
    |--
    (
    TT &&
    emp **
    ((SllPtrArray.full p n rows))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Module Type sll_ptr_array_Strategy_Correct.

  Axiom sll_ptr_array_strategy1_correctness : sll_ptr_array_strategy1.
  Axiom sll_ptr_array_strategy4_correctness : sll_ptr_array_strategy4.
  Axiom sll_ptr_array_strategy5_correctness : sll_ptr_array_strategy5.
  Axiom sll_ptr_array_strategy2_correctness : sll_ptr_array_strategy2.

End sll_ptr_array_Strategy_Correct.
