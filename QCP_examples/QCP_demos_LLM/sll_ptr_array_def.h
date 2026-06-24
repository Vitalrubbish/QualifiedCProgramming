struct list {
   int data;
   struct list *next;
};

/*@ Extern Coq (SllPtrArray::full : Z -> Z -> list (list Z) -> Assertion)
               (SllPtrArray::missing_i : Z -> Z -> Z -> Z -> list (list Z) -> Assertion)
               (sll : Z -> list Z -> Assertion)
               (sllseg: Z -> Z -> list Z -> Assertion)
               (sllbseg: Z -> Z -> list Z -> Assertion)
               (Znth: {A} -> Z -> list A -> A -> A)
               (Zlength: {A} -> list A -> Z)
               (replace_Znth: {A} -> Z -> A -> list A -> list A)
*/

/*@ Import Coq Require Import SimpleC.EE.QCP_demos_LLM.sll_lib */
/*@ Import Coq Require Import SimpleC.EE.QCP_demos_LLM.SllPtrArrayLib */

/*@ include strategies "sll_ptr_array.strategies" */
/*@ include strategies "sll.strategies" */
