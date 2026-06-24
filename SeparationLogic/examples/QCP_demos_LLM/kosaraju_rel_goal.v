Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
From MonadLib Require Export MonadLib.
From MonadLib.StateRelMonad Require Export StateRelMonad.
Export MonadNotation.
Local Open Scope monad.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap relations.
From FP Require Import PartialOrder_Setoid BourbakiWitt.
Require Import SimpleC.EE.QCP_demos_LLM.sll_lib.
Require Import SimpleC.EE.QCP_demos_LLM.SllPtrArrayLib.
Require Import SimpleC.EE.QCP_demos_LLM.kosaraju_rel_lib.
Local Open Scope sac.
From SimpleC.EE.QCP_demos_LLM Require Import safeexec_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import safeexec_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import int_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import int_array_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import uint_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import uint_array_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import undef_uint_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import undef_uint_array_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import array_shape_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import array_shape_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import sll_ptr_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import sll_ptr_array_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import sll_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import sll_strategy_proof.

(*----- Function kosaraju_num_vertices -----*)

Definition kosaraju_num_vertices_return_wit_1 := 
forall (X_low_level_spec: (unit -> (KSt -> Prop))) (PreH1 : (safeExec ATrue (dfs_finish (0)) X_low_level_spec )) ,
  TT && emp 
|--
  “ (safeExec ATrue (dfs_finish (0)) X_low_level_spec ) ”
  &&  emp
.

(*----- Function kosaraju_get_visited1 -----*)

Definition kosaraju_get_visited1_return_wit_1 := 
(
forall (u_pre: Z) (vis1_pre: Z) (n_pre: Z) (X_low_level_spec: (Z -> (KSt -> Prop))) (vis1_l_low_level_spec: (@list Z)) (PreH1 : (safeExec ATrue (kosaraju_get_visited1_rel (u_pre) (vis1_l_low_level_spec)) X_low_level_spec )) (PreH2 : (0 <= u_pre)) (PreH3 : (u_pre < n_pre)) (PreH4 : (n_pre <= INT_MAX)) ,
  (IntArray.full vis1_pre n_pre vis1_l_low_level_spec )
|--
  “ (safeExec ATrue (kosaraju_get_visited1_rel (u_pre) (vis1_l_low_level_spec)) X_low_level_spec ) ” 
  &&  “ ((Znth u_pre vis1_l_low_level_spec 0) = (Znth (u_pre) (vis1_l_low_level_spec) (0))) ”
  &&  (IntArray.full vis1_pre n_pre vis1_l_low_level_spec )
) \/
(
forall (u_pre: Z) (n_pre: Z) (X_low_level_spec: (Z -> (KSt -> Prop))) (vis1_l_low_level_spec: (@list Z)) (PreH1 : (safeExec ATrue (kosaraju_get_visited1_rel (u_pre) (vis1_l_low_level_spec)) X_low_level_spec )) (PreH2 : (0 <= u_pre)) (PreH3 : (u_pre < n_pre)) (PreH4 : (n_pre <= INT_MAX)) ,
  TT && emp 
|--
  “ ((Znth u_pre vis1_l_low_level_spec 0) = (Znth (u_pre) (vis1_l_low_level_spec) (0))) ”
  &&  emp
).

Definition kosaraju_get_visited1_return_wit_1_split_goal_1 := 
forall (u_pre: Z) (n_pre: Z) (X_low_level_spec: (Z -> (KSt -> Prop))) (vis1_l_low_level_spec: (@list Z)) (PreH1 : (safeExec ATrue (kosaraju_get_visited1_rel (u_pre) (vis1_l_low_level_spec)) X_low_level_spec )) (PreH2 : (0 <= u_pre)) (PreH3 : (u_pre < n_pre)) (PreH4 : (n_pre <= INT_MAX)) ,
  TT && emp 
|--
  “ ((Znth u_pre vis1_l_low_level_spec 0) = (Znth (u_pre) (vis1_l_low_level_spec) (0))) ”
.

Definition kosaraju_get_visited1_partial_solve_wit_1 := 
forall (u_pre: Z) (vis1_pre: Z) (n_pre: Z) (X_low_level_spec: (Z -> (KSt -> Prop))) (vis1_l_low_level_spec: (@list Z)) (PreH1 : (safeExec ATrue (kosaraju_get_visited1_rel (u_pre) (vis1_l_low_level_spec)) X_low_level_spec )) (PreH2 : (0 <= u_pre)) (PreH3 : (u_pre < n_pre)) (PreH4 : (n_pre <= INT_MAX)) ,
  (IntArray.full vis1_pre n_pre vis1_l_low_level_spec )
|--
  “ (safeExec ATrue (kosaraju_get_visited1_rel (u_pre) (vis1_l_low_level_spec)) X_low_level_spec ) ” 
  &&  “ (0 <= u_pre) ” 
  &&  “ (u_pre < n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ”
  &&  (((vis1_pre + (u_pre * sizeof(INT) ) )) # Int  |-> (Znth u_pre vis1_l_low_level_spec 0))
  **  (IntArray.missing_i vis1_pre u_pre 0 n_pre vis1_l_low_level_spec )
.

(*----- Function dfs1 -----*)

Definition dfs1_safety_wit_1 := 
forall (timer_p_pre: Z) (fin_pre: Z) (vis1_pre: Z) (radj_pre: Z) (n_pre: Z) (u_pre: Z) (radj_rows_low_level_spec: (@list (@list Z))) (X_low_level_spec: (unit -> (KSt -> Prop))) (timer_v_low_level_spec: Z) (fin_l_low_level_spec: (@list Z)) (vis1_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (PreH1 : (safeExec (pre_dfs1 (g_low_level_spec) (vis1_l_low_level_spec) (fin_l_low_level_spec) (timer_v_low_level_spec)) (dfs_finish (u_pre)) X_low_level_spec )) (PreH2 : (0 <= u_pre)) (PreH3 : (u_pre < n_pre)) (PreH4 : (n_pre <= INT_MAX)) ,
  ((( &( "timer_p" ) )) # Ptr  |-> timer_p_pre)
  **  ((( &( "fin" ) )) # Ptr  |-> fin_pre)
  **  ((( &( "vis1" ) )) # Ptr  |-> vis1_pre)
  **  ((( &( "radj" ) )) # Ptr  |-> radj_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "u" ) )) # Int  |-> u_pre)
  **  (SllPtrArray.full radj_pre n_pre radj_rows_low_level_spec )
  **  (IntArray.full vis1_pre n_pre vis1_l_low_level_spec )
  **  (IntArray.full fin_pre n_pre fin_l_low_level_spec )
  **  (IntArray.full timer_p_pre 1 (cons (timer_v_low_level_spec) ((@nil Z))) )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition dfs1_safety_wit_2 := 
forall (timer_p_pre: Z) (fin_pre: Z) (vis1_pre: Z) (radj_pre: Z) (n_pre: Z) (u_pre: Z) (radj_rows_low_level_spec: (@list (@list Z))) (X_low_level_spec: (unit -> (KSt -> Prop))) (g_low_level_spec: AdjGraph) (rem: (@list Z)) (cur: Z) (head: Z) (vis1_m: (@list Z)) (fin_m: (@list Z)) (timer_m: Z) (processed: (@list Z)) (PreH1 : (safeExec (pre_dfs1 (g_low_level_spec) (vis1_m) (fin_m) (timer_m)) (dfs_finish_from (u_pre) ((edges_of (u_pre) (processed)))) X_low_level_spec )) (PreH2 : (0 <= u_pre)) (PreH3 : (u_pre < n_pre)) (PreH4 : (n_pre <= INT_MAX)) ,
  ((( &( "u" ) )) # Int  |-> u_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "radj" ) )) # Ptr  |-> radj_pre)
  **  ((( &( "vis1" ) )) # Ptr  |-> vis1_pre)
  **  ((( &( "fin" ) )) # Ptr  |-> fin_pre)
  **  ((( &( "timer_p" ) )) # Ptr  |-> timer_p_pre)
  **  (SllPtrArray.missing_i radj_pre n_pre u_pre head radj_rows_low_level_spec )
  **  ((( &( "cur" ) )) # Ptr  |-> cur)
  **  (sllseg head cur processed )
  **  (sll cur rem )
  **  (IntArray.full vis1_pre n_pre vis1_m )
  **  (IntArray.full fin_pre n_pre fin_m )
  **  (IntArray.full timer_p_pre 1 (cons (timer_m) ((@nil Z))) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition dfs1_safety_wit_3 := 
forall (radj_rows_low_level_spec: (@list (@list Z))) (X_low_level_spec: (unit -> (KSt -> Prop))) (g_low_level_spec: AdjGraph) (head: Z) (processed: (@list Z)) (rem: (@list Z)) (vis1_m: (@list Z)) (fin_m: (@list Z)) (timer_m: Z) (vdata: Z) (rest: (@list Z)) (next_ptr: Z) (cur: Z) (n: Z) (u: Z) (radj: Z) (vis1: Z) (fin: Z) (timer_p: Z) (PreH1 : (cur <> 0)) (PreH2 : (0 <= vdata)) (PreH3 : (vdata < n)) (PreH4 : (n <= INT_MAX)) (PreH5 : (rem = (cons (vdata) (rest)))) (PreH6 : (safeExec (pre_dfs1 (g_low_level_spec) (vis1_m) (fin_m) (timer_m)) (dfs_finish_from (u) ((edges_of (u) (processed)))) X_low_level_spec )) ,
  (IntArray.full vis1 n vis1_m )
  **  ((( &( "cur" ) )) # Ptr  |-> cur)
  **  ((( &( "v" ) )) # Int  |-> vdata)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "u" ) )) # Int  |-> u)
  **  ((( &( "radj" ) )) # Ptr  |-> radj)
  **  (SllPtrArray.missing_i radj n u head radj_rows_low_level_spec )
  **  (sllseg head cur processed )
  **  ((&((cur)  # "list" ->ₛ "data")) # Int  |-> vdata)
  **  ((&((cur)  # "list" ->ₛ "next")) # Ptr  |-> next_ptr)
  **  (sll next_ptr rest )
  **  ((( &( "vis1" ) )) # Ptr  |-> vis1)
  **  ((( &( "fin" ) )) # Ptr  |-> fin)
  **  (IntArray.full fin n fin_m )
  **  ((( &( "timer_p" ) )) # Ptr  |-> timer_p)
  **  (IntArray.full timer_p 1 (cons (timer_m) ((@nil Z))) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition dfs1_safety_wit_4 := 
forall (timer_p_pre: Z) (fin_pre: Z) (vis1_pre: Z) (radj_pre: Z) (n_pre: Z) (u_pre: Z) (radj_rows_low_level_spec: (@list (@list Z))) (X_low_level_spec: (unit -> (KSt -> Prop))) (g_low_level_spec: AdjGraph) (rem: (@list Z)) (cur: Z) (head: Z) (vis1_m: (@list Z)) (fin_m: (@list Z)) (timer_m: Z) (processed: (@list Z)) (PreH1 : (cur = 0)) (PreH2 : (safeExec (pre_dfs1 (g_low_level_spec) (vis1_m) (fin_m) (timer_m)) (dfs_finish_from (u_pre) ((edges_of (u_pre) (processed)))) X_low_level_spec )) (PreH3 : (0 <= u_pre)) (PreH4 : (u_pre < n_pre)) (PreH5 : (n_pre <= INT_MAX)) ,
  ((( &( "t0" ) )) # Int  |->_)
  **  ((( &( "u" ) )) # Int  |-> u_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "radj" ) )) # Ptr  |-> radj_pre)
  **  ((( &( "vis1" ) )) # Ptr  |-> vis1_pre)
  **  ((( &( "fin" ) )) # Ptr  |-> fin_pre)
  **  ((( &( "timer_p" ) )) # Ptr  |-> timer_p_pre)
  **  (SllPtrArray.missing_i radj_pre n_pre u_pre head radj_rows_low_level_spec )
  **  ((( &( "cur" ) )) # Ptr  |-> cur)
  **  (sllseg head cur processed )
  **  (sll cur rem )
  **  (IntArray.full vis1_pre n_pre vis1_m )
  **  (IntArray.full fin_pre n_pre fin_m )
  **  (IntArray.full timer_p_pre 1 (cons (timer_m) ((@nil Z))) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition dfs1_safety_wit_5 := 
forall (timer_p_pre: Z) (fin_pre: Z) (vis1_pre: Z) (radj_pre: Z) (n_pre: Z) (u_pre: Z) (radj_rows_low_level_spec: (@list (@list Z))) (X_low_level_spec: (unit -> (KSt -> Prop))) (g_low_level_spec: AdjGraph) (head: Z) (vis1_m: (@list Z)) (fin_m: (@list Z)) (timer_m: Z) (fin_m_set: (@list Z)) (timer_m_set: Z) (PreH1 : (0 <= u_pre)) (PreH2 : (u_pre < n_pre)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (fin_m_set = (replace_Znth (u_pre) (timer_m) (fin_m)))) (PreH5 : (timer_m_set = (timer_m + 1 ))) (PreH6 : (safeExec (pre_dfs1 (g_low_level_spec) (vis1_m) (fin_m_set) (timer_m_set)) (return (tt)) X_low_level_spec )) ,
  (IntArray.full fin_pre n_pre (replace_Znth (u_pre) (timer_m) (fin_m_set)) )
  **  ((( &( "u" ) )) # Int  |-> u_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "radj" ) )) # Ptr  |-> radj_pre)
  **  ((( &( "vis1" ) )) # Ptr  |-> vis1_pre)
  **  ((( &( "fin" ) )) # Ptr  |-> fin_pre)
  **  ((( &( "timer_p" ) )) # Ptr  |-> timer_p_pre)
  **  ((( &( "t0" ) )) # Int  |-> timer_m)
  **  (SllPtrArray.missing_i radj_pre n_pre u_pre head radj_rows_low_level_spec )
  **  (sll head (Znth (u_pre) (radj_rows_low_level_spec) ((@nil Z))) )
  **  ((( &( "cur" ) )) # Ptr  |-> 0)
  **  (IntArray.full vis1_pre n_pre vis1_m )
  **  (IntArray.full timer_p_pre 1 (cons (timer_m) ((@nil Z))) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition dfs1_safety_wit_6 := 
(
forall (timer_p_pre: Z) (fin_pre: Z) (vis1_pre: Z) (radj_pre: Z) (n_pre: Z) (u_pre: Z) (radj_rows_low_level_spec: (@list (@list Z))) (X_low_level_spec: (unit -> (KSt -> Prop))) (g_low_level_spec: AdjGraph) (head: Z) (vis1_m: (@list Z)) (fin_m: (@list Z)) (timer_m: Z) (fin_m_set: (@list Z)) (timer_m_set: Z) (PreH1 : (0 <= u_pre)) (PreH2 : (u_pre < n_pre)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (fin_m_set = (replace_Znth (u_pre) (timer_m) (fin_m)))) (PreH5 : (timer_m_set = (timer_m + 1 ))) (PreH6 : (safeExec (pre_dfs1 (g_low_level_spec) (vis1_m) (fin_m_set) (timer_m_set)) (return (tt)) X_low_level_spec )) ,
  (IntArray.full fin_pre n_pre (replace_Znth (u_pre) (timer_m) (fin_m_set)) )
  **  ((( &( "u" ) )) # Int  |-> u_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "radj" ) )) # Ptr  |-> radj_pre)
  **  ((( &( "vis1" ) )) # Ptr  |-> vis1_pre)
  **  ((( &( "fin" ) )) # Ptr  |-> fin_pre)
  **  ((( &( "timer_p" ) )) # Ptr  |-> timer_p_pre)
  **  ((( &( "t0" ) )) # Int  |-> timer_m)
  **  (SllPtrArray.missing_i radj_pre n_pre u_pre head radj_rows_low_level_spec )
  **  (sll head (Znth (u_pre) (radj_rows_low_level_spec) ((@nil Z))) )
  **  ((( &( "cur" ) )) # Ptr  |-> 0)
  **  (IntArray.full vis1_pre n_pre vis1_m )
  **  (IntArray.full timer_p_pre 1 (cons (timer_m) ((@nil Z))) )
|--
  “ ((timer_m + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (timer_m + 1 )) ”
) \/
(
forall (timer_p_pre: Z) (fin_pre: Z) (vis1_pre: Z) (radj_pre: Z) (n_pre: Z) (u_pre: Z) (radj_rows_low_level_spec: (@list (@list Z))) (X_low_level_spec: (unit -> (KSt -> Prop))) (g_low_level_spec: AdjGraph) (head: Z) (vis1_m: (@list Z)) (fin_m: (@list Z)) (timer_m: Z) (fin_m_set: (@list Z)) (timer_m_set: Z) (PreH1 : (0 <= u_pre)) (PreH2 : (u_pre < n_pre)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (fin_m_set = (replace_Znth (u_pre) (timer_m) (fin_m)))) (PreH5 : (timer_m_set = (timer_m + 1 ))) (PreH6 : (safeExec (pre_dfs1 (g_low_level_spec) (vis1_m) (fin_m_set) (timer_m_set)) (return (tt)) X_low_level_spec )) ,
  (IntArray.full fin_pre n_pre (replace_Znth (u_pre) (timer_m) (fin_m_set)) )
  **  ((( &( "u" ) )) # Int  |-> u_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "radj" ) )) # Ptr  |-> radj_pre)
  **  ((( &( "vis1" ) )) # Ptr  |-> vis1_pre)
  **  ((( &( "fin" ) )) # Ptr  |-> fin_pre)
  **  ((( &( "timer_p" ) )) # Ptr  |-> timer_p_pre)
  **  ((( &( "t0" ) )) # Int  |-> timer_m)
  **  (SllPtrArray.missing_i radj_pre n_pre u_pre head radj_rows_low_level_spec )
  **  (sll head (Znth (u_pre) (radj_rows_low_level_spec) ((@nil Z))) )
  **  ((( &( "cur" ) )) # Ptr  |-> 0)
  **  (IntArray.full vis1_pre n_pre vis1_m )
  **  (IntArray.full timer_p_pre 1 (cons (timer_m) ((@nil Z))) )
|--
  “ ((timer_m + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (timer_m + 1 )) ”
).

Definition dfs1_safety_wit_6_split_goal_1 := 
forall (timer_p_pre: Z) (fin_pre: Z) (vis1_pre: Z) (radj_pre: Z) (n_pre: Z) (u_pre: Z) (radj_rows_low_level_spec: (@list (@list Z))) (X_low_level_spec: (unit -> (KSt -> Prop))) (g_low_level_spec: AdjGraph) (head: Z) (vis1_m: (@list Z)) (fin_m: (@list Z)) (timer_m: Z) (fin_m_set: (@list Z)) (timer_m_set: Z) (PreH1 : (0 <= u_pre)) (PreH2 : (u_pre < n_pre)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (fin_m_set = (replace_Znth (u_pre) (timer_m) (fin_m)))) (PreH5 : (timer_m_set = (timer_m + 1 ))) (PreH6 : (safeExec (pre_dfs1 (g_low_level_spec) (vis1_m) (fin_m_set) (timer_m_set)) (return (tt)) X_low_level_spec )) ,
  (IntArray.full fin_pre n_pre (replace_Znth (u_pre) (timer_m) (fin_m_set)) )
  **  ((( &( "u" ) )) # Int  |-> u_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "radj" ) )) # Ptr  |-> radj_pre)
  **  ((( &( "vis1" ) )) # Ptr  |-> vis1_pre)
  **  ((( &( "fin" ) )) # Ptr  |-> fin_pre)
  **  ((( &( "timer_p" ) )) # Ptr  |-> timer_p_pre)
  **  ((( &( "t0" ) )) # Int  |-> timer_m)
  **  (SllPtrArray.missing_i radj_pre n_pre u_pre head radj_rows_low_level_spec )
  **  (sll head (Znth (u_pre) (radj_rows_low_level_spec) ((@nil Z))) )
  **  ((( &( "cur" ) )) # Ptr  |-> 0)
  **  (IntArray.full vis1_pre n_pre vis1_m )
  **  (IntArray.full timer_p_pre 1 (cons (timer_m) ((@nil Z))) )
|--
  “ ((timer_m + 1 ) <= INT_MAX) ”
.

Definition dfs1_safety_wit_6_split_goal_2 := 
forall (timer_p_pre: Z) (fin_pre: Z) (vis1_pre: Z) (radj_pre: Z) (n_pre: Z) (u_pre: Z) (radj_rows_low_level_spec: (@list (@list Z))) (X_low_level_spec: (unit -> (KSt -> Prop))) (g_low_level_spec: AdjGraph) (head: Z) (vis1_m: (@list Z)) (fin_m: (@list Z)) (timer_m: Z) (fin_m_set: (@list Z)) (timer_m_set: Z) (PreH1 : (0 <= u_pre)) (PreH2 : (u_pre < n_pre)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (fin_m_set = (replace_Znth (u_pre) (timer_m) (fin_m)))) (PreH5 : (timer_m_set = (timer_m + 1 ))) (PreH6 : (safeExec (pre_dfs1 (g_low_level_spec) (vis1_m) (fin_m_set) (timer_m_set)) (return (tt)) X_low_level_spec )) ,
  (IntArray.full fin_pre n_pre (replace_Znth (u_pre) (timer_m) (fin_m_set)) )
  **  ((( &( "u" ) )) # Int  |-> u_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "radj" ) )) # Ptr  |-> radj_pre)
  **  ((( &( "vis1" ) )) # Ptr  |-> vis1_pre)
  **  ((( &( "fin" ) )) # Ptr  |-> fin_pre)
  **  ((( &( "timer_p" ) )) # Ptr  |-> timer_p_pre)
  **  ((( &( "t0" ) )) # Int  |-> timer_m)
  **  (SllPtrArray.missing_i radj_pre n_pre u_pre head radj_rows_low_level_spec )
  **  (sll head (Znth (u_pre) (radj_rows_low_level_spec) ((@nil Z))) )
  **  ((( &( "cur" ) )) # Ptr  |-> 0)
  **  (IntArray.full vis1_pre n_pre vis1_m )
  **  (IntArray.full timer_p_pre 1 (cons (timer_m) ((@nil Z))) )
|--
  “ ((INT_MIN) <= (timer_m + 1 )) ”
.

Definition dfs1_safety_wit_7 := 
forall (timer_p_pre: Z) (fin_pre: Z) (vis1_pre: Z) (radj_pre: Z) (n_pre: Z) (u_pre: Z) (radj_rows_low_level_spec: (@list (@list Z))) (X_low_level_spec: (unit -> (KSt -> Prop))) (g_low_level_spec: AdjGraph) (head: Z) (vis1_m: (@list Z)) (fin_m: (@list Z)) (timer_m: Z) (fin_m_set: (@list Z)) (timer_m_set: Z) (PreH1 : (0 <= u_pre)) (PreH2 : (u_pre < n_pre)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (fin_m_set = (replace_Znth (u_pre) (timer_m) (fin_m)))) (PreH5 : (timer_m_set = (timer_m + 1 ))) (PreH6 : (safeExec (pre_dfs1 (g_low_level_spec) (vis1_m) (fin_m_set) (timer_m_set)) (return (tt)) X_low_level_spec )) ,
  (IntArray.full fin_pre n_pre (replace_Znth (u_pre) (timer_m) (fin_m_set)) )
  **  ((( &( "u" ) )) # Int  |-> u_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "radj" ) )) # Ptr  |-> radj_pre)
  **  ((( &( "vis1" ) )) # Ptr  |-> vis1_pre)
  **  ((( &( "fin" ) )) # Ptr  |-> fin_pre)
  **  ((( &( "timer_p" ) )) # Ptr  |-> timer_p_pre)
  **  ((( &( "t0" ) )) # Int  |-> timer_m)
  **  (SllPtrArray.missing_i radj_pre n_pre u_pre head radj_rows_low_level_spec )
  **  (sll head (Znth (u_pre) (radj_rows_low_level_spec) ((@nil Z))) )
  **  ((( &( "cur" ) )) # Ptr  |-> 0)
  **  (IntArray.full vis1_pre n_pre vis1_m )
  **  (IntArray.full timer_p_pre 1 (cons (timer_m) ((@nil Z))) )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition dfs1_entail_wit_1 := 
(
forall (timer_p_pre: Z) (fin_pre: Z) (vis1_pre: Z) (radj_pre: Z) (n_pre: Z) (u_pre: Z) (radj_rows_low_level_spec: (@list (@list Z))) (X_low_level_spec: (unit -> (KSt -> Prop))) (timer_v_low_level_spec: Z) (fin_l_low_level_spec: (@list Z)) (vis1_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (row_ptr: Z) (PreH1 : (safeExec (pre_dfs1 (g_low_level_spec) (vis1_l_low_level_spec) (fin_l_low_level_spec) (timer_v_low_level_spec)) (dfs_finish (u_pre)) X_low_level_spec )) (PreH2 : (0 <= u_pre)) (PreH3 : (u_pre < n_pre)) (PreH4 : (n_pre <= INT_MAX)) ,
  (SllPtrArray.full radj_pre n_pre radj_rows_low_level_spec )
  **  (IntArray.full vis1_pre n_pre (replace_Znth (u_pre) (1) (vis1_l_low_level_spec)) )
  **  (IntArray.full fin_pre n_pre fin_l_low_level_spec )
  **  (IntArray.full timer_p_pre 1 (cons (timer_v_low_level_spec) ((@nil Z))) )
|--
  EX (rem: (@list Z))  (head: Z)  (vis1_m: (@list Z))  (fin_m: (@list Z))  (timer_m: Z)  (processed: (@list Z)) ,
  “ (safeExec (pre_dfs1 (g_low_level_spec) (vis1_m) (fin_m) (timer_m)) (dfs_finish_from (u_pre) ((edges_of (u_pre) (processed)))) X_low_level_spec ) ” 
  &&  “ (0 <= u_pre) ” 
  &&  “ (u_pre < n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ”
  &&  (SllPtrArray.missing_i radj_pre n_pre u_pre head radj_rows_low_level_spec )
  **  (sllseg head row_ptr processed )
  **  (sll row_ptr rem )
  **  (IntArray.full vis1_pre n_pre vis1_m )
  **  (IntArray.full fin_pre n_pre fin_m )
  **  (IntArray.full timer_p_pre 1 (cons (timer_m) ((@nil Z))) )
) \/
(
forall (radj_pre: Z) (n_pre: Z) (u_pre: Z) (radj_rows_low_level_spec: (@list (@list Z))) (X_low_level_spec: (unit -> (KSt -> Prop))) (timer_v_low_level_spec: Z) (fin_l_low_level_spec: (@list Z)) (vis1_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (row_ptr: Z) (PreH1 : (safeExec (pre_dfs1 (g_low_level_spec) (vis1_l_low_level_spec) (fin_l_low_level_spec) (timer_v_low_level_spec)) (dfs_finish (u_pre)) X_low_level_spec )) (PreH2 : (0 <= u_pre)) (PreH3 : (u_pre < n_pre)) (PreH4 : (n_pre <= INT_MAX)) ,
  (SllPtrArray.full radj_pre n_pre radj_rows_low_level_spec )
|--
  EX (rem: (@list Z))  (head: Z)  (timer_m: Z)  (processed: (@list Z)) ,
  “ ((cons (timer_v_low_level_spec) ((@nil Z))) = (cons (timer_m) ((@nil Z)))) ” 
  &&  “ (safeExec (pre_dfs1 (g_low_level_spec) ((replace_Znth (u_pre) (1) (vis1_l_low_level_spec))) (fin_l_low_level_spec) (timer_m)) (dfs_finish_from (u_pre) ((edges_of (u_pre) (processed)))) X_low_level_spec ) ” 
  &&  “ (0 <= u_pre) ” 
  &&  “ (u_pre < n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ”
  &&  (SllPtrArray.missing_i radj_pre n_pre u_pre head radj_rows_low_level_spec )
  **  (sllseg head row_ptr processed )
  **  (sll row_ptr rem )
).

Definition dfs1_entail_wit_2 := 
(
forall (timer_p_pre: Z) (fin_pre: Z) (vis1_pre: Z) (radj_pre: Z) (n_pre: Z) (u_pre: Z) (radj_rows_low_level_spec: (@list (@list Z))) (X_low_level_spec: (unit -> (KSt -> Prop))) (g_low_level_spec: AdjGraph) (cur: Z) (head: Z) (processed: (@list Z)) (rem: (@list Z)) (vis1_m: (@list Z)) (fin_m: (@list Z)) (timer_m: Z) (PreH1 : (cur <> 0)) (PreH2 : (safeExec (pre_dfs1 (g_low_level_spec) (vis1_m) (fin_m) (timer_m)) (dfs_finish_from (u_pre) ((edges_of (u_pre) (processed)))) X_low_level_spec )) (PreH3 : (0 <= u_pre)) (PreH4 : (u_pre < n_pre)) (PreH5 : (n_pre <= INT_MAX)) ,
  ((( &( "v" ) )) # Int  |->_)
  **  (SllPtrArray.missing_i radj_pre n_pre u_pre head radj_rows_low_level_spec )
  **  (sllseg head cur processed )
  **  (sll cur rem )
  **  (IntArray.full vis1_pre n_pre vis1_m )
  **  (IntArray.full fin_pre n_pre fin_m )
  **  (IntArray.full timer_p_pre 1 (cons (timer_m) ((@nil Z))) )
|--
  EX (next_ptr: Z)  (rest: (@list Z))  (vdata: Z) ,
  “ (cur <> 0) ” 
  &&  “ (0 <= vdata) ” 
  &&  “ (vdata < n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (rem = (cons (vdata) (rest))) ” 
  &&  “ (safeExec (pre_dfs1 (g_low_level_spec) (vis1_m) (fin_m) (timer_m)) (dfs_finish_from (u_pre) ((edges_of (u_pre) (processed)))) X_low_level_spec ) ”
  &&  ((( &( "v" ) )) # Int  |-> vdata)
  **  (SllPtrArray.missing_i radj_pre n_pre u_pre head radj_rows_low_level_spec )
  **  (sllseg head cur processed )
  **  ((&((cur)  # "list" ->ₛ "data")) # Int  |-> vdata)
  **  ((&((cur)  # "list" ->ₛ "next")) # Ptr  |-> next_ptr)
  **  (sll next_ptr rest )
  **  (IntArray.full vis1_pre n_pre vis1_m )
  **  (IntArray.full fin_pre n_pre fin_m )
  **  (IntArray.full timer_p_pre 1 (cons (timer_m) ((@nil Z))) )
) \/
(
forall (n_pre: Z) (u_pre: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (g_low_level_spec: AdjGraph) (cur: Z) (head: Z) (processed: (@list Z)) (rem: (@list Z)) (vis1_m: (@list Z)) (fin_m: (@list Z)) (timer_m: Z) (x: Z) (l0: (@list Z)) (PreH1 : (rem = (cons (x) (l0)))) (PreH2 : (cur <> 0)) (PreH3 : (safeExec (pre_dfs1 (g_low_level_spec) (vis1_m) (fin_m) (timer_m)) (dfs_finish_from (u_pre) ((edges_of (u_pre) (processed)))) X_low_level_spec )) (PreH4 : (0 <= u_pre)) (PreH5 : (u_pre < n_pre)) (PreH6 : (n_pre <= INT_MAX)) ,
  ((( &( "v" ) )) # Int  |->_)
  **  (sllseg head cur processed )
|--
  “ (x < n_pre) ” 
  &&  “ (0 <= x) ”
  &&  ((( &( "v" ) )) # Int  |-> x)
  **  (sllseg head cur processed )
).

Definition dfs1_entail_wit_2_split_goal_1 := 
forall (n_pre: Z) (u_pre: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (g_low_level_spec: AdjGraph) (cur: Z) (head: Z) (processed: (@list Z)) (rem: (@list Z)) (vis1_m: (@list Z)) (fin_m: (@list Z)) (timer_m: Z) (x: Z) (l0: (@list Z)) (PreH1 : (rem = (cons (x) (l0)))) (PreH2 : (cur <> 0)) (PreH3 : (safeExec (pre_dfs1 (g_low_level_spec) (vis1_m) (fin_m) (timer_m)) (dfs_finish_from (u_pre) ((edges_of (u_pre) (processed)))) X_low_level_spec )) (PreH4 : (0 <= u_pre)) (PreH5 : (u_pre < n_pre)) (PreH6 : (n_pre <= INT_MAX)) ,
  ((( &( "v" ) )) # Int  |->_)
  **  (sllseg head cur processed )
|--
  “ (x < n_pre) ”
.

Definition dfs1_entail_wit_2_split_goal_2 := 
forall (n_pre: Z) (u_pre: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (g_low_level_spec: AdjGraph) (cur: Z) (head: Z) (processed: (@list Z)) (rem: (@list Z)) (vis1_m: (@list Z)) (fin_m: (@list Z)) (timer_m: Z) (x: Z) (l0: (@list Z)) (PreH1 : (rem = (cons (x) (l0)))) (PreH2 : (cur <> 0)) (PreH3 : (safeExec (pre_dfs1 (g_low_level_spec) (vis1_m) (fin_m) (timer_m)) (dfs_finish_from (u_pre) ((edges_of (u_pre) (processed)))) X_low_level_spec )) (PreH4 : (0 <= u_pre)) (PreH5 : (u_pre < n_pre)) (PreH6 : (n_pre <= INT_MAX)) ,
  ((( &( "v" ) )) # Int  |->_)
  **  (sllseg head cur processed )
|--
  “ (0 <= x) ”
.

Definition dfs1_entail_wit_2_split_goal_spatial := 
forall (n_pre: Z) (u_pre: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (g_low_level_spec: AdjGraph) (cur: Z) (head: Z) (processed: (@list Z)) (rem: (@list Z)) (vis1_m: (@list Z)) (fin_m: (@list Z)) (timer_m: Z) (x: Z) (l0: (@list Z)) (PreH1 : (rem = (cons (x) (l0)))) (PreH2 : (cur <> 0)) (PreH3 : (safeExec (pre_dfs1 (g_low_level_spec) (vis1_m) (fin_m) (timer_m)) (dfs_finish_from (u_pre) ((edges_of (u_pre) (processed)))) X_low_level_spec )) (PreH4 : (0 <= u_pre)) (PreH5 : (u_pre < n_pre)) (PreH6 : (n_pre <= INT_MAX)) ,
  ((( &( "v" ) )) # Int  |->_)
  **  (sllseg head cur processed )
|--
  ((( &( "v" ) )) # Int  |-> x)
  **  (sllseg head cur processed )
.

Definition dfs1_entail_wit_3 := 
(
forall (timer_p_pre: Z) (fin_pre: Z) (vis1_pre: Z) (radj_pre: Z) (n_pre: Z) (u_pre: Z) (radj_rows_low_level_spec: (@list (@list Z))) (X_low_level_spec: (unit -> (KSt -> Prop))) (g_low_level_spec: AdjGraph) (head: Z) (processed: (@list Z)) (rem: (@list Z)) (vis1_m: (@list Z)) (fin_m: (@list Z)) (timer_m: Z) (vdata: Z) (rest: (@list Z)) (next_ptr: Z) (cur: Z) (n: Z) (u: Z) (radj: Z) (vis1: Z) (fin: Z) (timer_p: Z) (PreH1 : ((Znth vdata vis1_m 0) = 0)) (PreH2 : (cur <> 0)) (PreH3 : (0 <= vdata)) (PreH4 : (vdata < n)) (PreH5 : (n <= INT_MAX)) (PreH6 : (rem = (cons (vdata) (rest)))) (PreH7 : (safeExec (pre_dfs1 (g_low_level_spec) (vis1_m) (fin_m) (timer_m)) (dfs_finish_from (u) ((edges_of (u) (processed)))) X_low_level_spec )) ,
  (IntArray.full vis1 n vis1_m )
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "u" ) )) # Int  |-> u)
  **  ((( &( "radj" ) )) # Ptr  |-> radj)
  **  (SllPtrArray.missing_i radj n u head radj_rows_low_level_spec )
  **  (sllseg head cur processed )
  **  ((&((cur)  # "list" ->ₛ "data")) # Int  |-> vdata)
  **  ((&((cur)  # "list" ->ₛ "next")) # Ptr  |-> next_ptr)
  **  (sll next_ptr rest )
  **  ((( &( "vis1" ) )) # Ptr  |-> vis1)
  **  ((( &( "fin" ) )) # Ptr  |-> fin)
  **  (IntArray.full fin n fin_m )
  **  ((( &( "timer_p" ) )) # Ptr  |-> timer_p)
  **  (IntArray.full timer_p 1 (cons (timer_m) ((@nil Z))) )
|--
  “ (cur <> 0) ” 
  &&  “ (0 <= u_pre) ” 
  &&  “ (u_pre < n_pre) ” 
  &&  “ (0 <= vdata) ” 
  &&  “ (vdata < n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ ((Znth (vdata) (vis1_m) (0)) = 0) ” 
  &&  “ (safeExec (pre_dfs1 (g_low_level_spec) (vis1_m) (fin_m) (timer_m)) (dfs_finish (vdata)) X_low_level_spec ) ”
  &&  ((( &( "u" ) )) # Int  |-> u_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "radj" ) )) # Ptr  |-> radj_pre)
  **  ((( &( "vis1" ) )) # Ptr  |-> vis1_pre)
  **  ((( &( "fin" ) )) # Ptr  |-> fin_pre)
  **  ((( &( "timer_p" ) )) # Ptr  |-> timer_p_pre)
  **  (SllPtrArray.full radj_pre n_pre radj_rows_low_level_spec )
  **  (IntArray.full vis1_pre n_pre vis1_m )
  **  (IntArray.full fin_pre n_pre fin_m )
  **  (IntArray.full timer_p_pre 1 (cons (timer_m) ((@nil Z))) )
) \/
(
forall (timer_p_pre: Z) (fin_pre: Z) (vis1_pre: Z) (radj_pre: Z) (n_pre: Z) (u_pre: Z) (radj_rows_low_level_spec: (@list (@list Z))) (X_low_level_spec: (unit -> (KSt -> Prop))) (g_low_level_spec: AdjGraph) (head: Z) (processed: (@list Z)) (rem: (@list Z)) (vis1_m: (@list Z)) (fin_m: (@list Z)) (timer_m: Z) (vdata: Z) (rest: (@list Z)) (next_ptr: Z) (cur: Z) (n: Z) (u: Z) (radj: Z) (vis1: Z) (fin: Z) (timer_p: Z) (PreH1 : (vdata <= INT_MAX)) (PreH2 : (vdata >= INT_MIN)) (PreH3 : ((Znth vdata vis1_m 0) = 0)) (PreH4 : (cur <> 0)) (PreH5 : (0 <= vdata)) (PreH6 : (vdata < n)) (PreH7 : (n <= INT_MAX)) (PreH8 : (rem = (cons (vdata) (rest)))) (PreH9 : (safeExec (pre_dfs1 (g_low_level_spec) (vis1_m) (fin_m) (timer_m)) (dfs_finish_from (u) ((edges_of (u) (processed)))) X_low_level_spec )) ,
  (IntArray.full vis1 n vis1_m )
  **  (SllPtrArray.missing_i radj n u head radj_rows_low_level_spec )
  **  (sllseg head cur processed )
  **  ((&((cur)  # "list" ->ₛ "data")) # Int  |-> vdata)
  **  ((&((cur)  # "list" ->ₛ "next")) # Ptr  |-> next_ptr)
  **  (sll next_ptr rest )
  **  (IntArray.full fin n fin_m )
  **  (IntArray.full timer_p 1 (cons (timer_m) ((@nil Z))) )
|--
  “ (safeExec (pre_dfs1 (g_low_level_spec) (vis1_m) (fin_m) (timer_m)) (dfs_finish (vdata)) X_low_level_spec ) ” 
  &&  “ ((Znth (vdata) (vis1_m) (0)) = 0) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (vdata < n_pre) ” 
  &&  “ (u_pre < n_pre) ” 
  &&  “ (0 <= u_pre) ” 
  &&  “ (n = n_pre) ” 
  &&  “ (u = u_pre) ” 
  &&  “ (radj = radj_pre) ” 
  &&  “ (vis1 = vis1_pre) ” 
  &&  “ (fin = fin_pre) ” 
  &&  “ (timer_p = timer_p_pre) ”
  &&  (SllPtrArray.full radj_pre n_pre radj_rows_low_level_spec )
  **  (IntArray.full vis1_pre n_pre vis1_m )
  **  (IntArray.full fin_pre n_pre fin_m )
  **  (IntArray.full timer_p_pre 1 (cons (timer_m) ((@nil Z))) )
).

Definition dfs1_entail_wit_3_split_goal_1 := 
forall (radj_rows_low_level_spec: (@list (@list Z))) (X_low_level_spec: (unit -> (KSt -> Prop))) (g_low_level_spec: AdjGraph) (head: Z) (processed: (@list Z)) (rem: (@list Z)) (vis1_m: (@list Z)) (fin_m: (@list Z)) (timer_m: Z) (vdata: Z) (rest: (@list Z)) (next_ptr: Z) (cur: Z) (n: Z) (u: Z) (radj: Z) (vis1: Z) (fin: Z) (timer_p: Z) (PreH1 : (vdata <= INT_MAX)) (PreH2 : (vdata >= INT_MIN)) (PreH3 : ((Znth vdata vis1_m 0) = 0)) (PreH4 : (cur <> 0)) (PreH5 : (0 <= vdata)) (PreH6 : (vdata < n)) (PreH7 : (n <= INT_MAX)) (PreH8 : (rem = (cons (vdata) (rest)))) (PreH9 : (safeExec (pre_dfs1 (g_low_level_spec) (vis1_m) (fin_m) (timer_m)) (dfs_finish_from (u) ((edges_of (u) (processed)))) X_low_level_spec )) ,
  (IntArray.full vis1 n vis1_m )
  **  (SllPtrArray.missing_i radj n u head radj_rows_low_level_spec )
  **  (sllseg head cur processed )
  **  ((&((cur)  # "list" ->ₛ "data")) # Int  |-> vdata)
  **  ((&((cur)  # "list" ->ₛ "next")) # Ptr  |-> next_ptr)
  **  (sll next_ptr rest )
  **  (IntArray.full fin n fin_m )
  **  (IntArray.full timer_p 1 (cons (timer_m) ((@nil Z))) )
|--
  “ (safeExec (pre_dfs1 (g_low_level_spec) (vis1_m) (fin_m) (timer_m)) (dfs_finish (vdata)) X_low_level_spec ) ”
.

Definition dfs1_entail_wit_3_split_goal_2 := 
forall (radj_rows_low_level_spec: (@list (@list Z))) (X_low_level_spec: (unit -> (KSt -> Prop))) (g_low_level_spec: AdjGraph) (head: Z) (processed: (@list Z)) (rem: (@list Z)) (vis1_m: (@list Z)) (fin_m: (@list Z)) (timer_m: Z) (vdata: Z) (rest: (@list Z)) (next_ptr: Z) (cur: Z) (n: Z) (u: Z) (radj: Z) (vis1: Z) (fin: Z) (timer_p: Z) (PreH1 : (vdata <= INT_MAX)) (PreH2 : (vdata >= INT_MIN)) (PreH3 : ((Znth vdata vis1_m 0) = 0)) (PreH4 : (cur <> 0)) (PreH5 : (0 <= vdata)) (PreH6 : (vdata < n)) (PreH7 : (n <= INT_MAX)) (PreH8 : (rem = (cons (vdata) (rest)))) (PreH9 : (safeExec (pre_dfs1 (g_low_level_spec) (vis1_m) (fin_m) (timer_m)) (dfs_finish_from (u) ((edges_of (u) (processed)))) X_low_level_spec )) ,
  (IntArray.full vis1 n vis1_m )
  **  (SllPtrArray.missing_i radj n u head radj_rows_low_level_spec )
  **  (sllseg head cur processed )
  **  ((&((cur)  # "list" ->ₛ "data")) # Int  |-> vdata)
  **  ((&((cur)  # "list" ->ₛ "next")) # Ptr  |-> next_ptr)
  **  (sll next_ptr rest )
  **  (IntArray.full fin n fin_m )
  **  (IntArray.full timer_p 1 (cons (timer_m) ((@nil Z))) )
|--
  “ ((Znth (vdata) (vis1_m) (0)) = 0) ”
.

Definition dfs1_entail_wit_3_split_goal_3 := 
forall (n_pre: Z) (radj_rows_low_level_spec: (@list (@list Z))) (X_low_level_spec: (unit -> (KSt -> Prop))) (g_low_level_spec: AdjGraph) (head: Z) (processed: (@list Z)) (rem: (@list Z)) (vis1_m: (@list Z)) (fin_m: (@list Z)) (timer_m: Z) (vdata: Z) (rest: (@list Z)) (next_ptr: Z) (cur: Z) (n: Z) (u: Z) (radj: Z) (vis1: Z) (fin: Z) (timer_p: Z) (PreH1 : (vdata <= INT_MAX)) (PreH2 : (vdata >= INT_MIN)) (PreH3 : ((Znth vdata vis1_m 0) = 0)) (PreH4 : (cur <> 0)) (PreH5 : (0 <= vdata)) (PreH6 : (vdata < n)) (PreH7 : (n <= INT_MAX)) (PreH8 : (rem = (cons (vdata) (rest)))) (PreH9 : (safeExec (pre_dfs1 (g_low_level_spec) (vis1_m) (fin_m) (timer_m)) (dfs_finish_from (u) ((edges_of (u) (processed)))) X_low_level_spec )) ,
  (IntArray.full vis1 n vis1_m )
  **  (SllPtrArray.missing_i radj n u head radj_rows_low_level_spec )
  **  (sllseg head cur processed )
  **  ((&((cur)  # "list" ->ₛ "data")) # Int  |-> vdata)
  **  ((&((cur)  # "list" ->ₛ "next")) # Ptr  |-> next_ptr)
  **  (sll next_ptr rest )
  **  (IntArray.full fin n fin_m )
  **  (IntArray.full timer_p 1 (cons (timer_m) ((@nil Z))) )
|--
  “ (n_pre <= INT_MAX) ”
.

Definition dfs1_entail_wit_3_split_goal_4 := 
forall (n_pre: Z) (radj_rows_low_level_spec: (@list (@list Z))) (X_low_level_spec: (unit -> (KSt -> Prop))) (g_low_level_spec: AdjGraph) (head: Z) (processed: (@list Z)) (rem: (@list Z)) (vis1_m: (@list Z)) (fin_m: (@list Z)) (timer_m: Z) (vdata: Z) (rest: (@list Z)) (next_ptr: Z) (cur: Z) (n: Z) (u: Z) (radj: Z) (vis1: Z) (fin: Z) (timer_p: Z) (PreH1 : (vdata <= INT_MAX)) (PreH2 : (vdata >= INT_MIN)) (PreH3 : ((Znth vdata vis1_m 0) = 0)) (PreH4 : (cur <> 0)) (PreH5 : (0 <= vdata)) (PreH6 : (vdata < n)) (PreH7 : (n <= INT_MAX)) (PreH8 : (rem = (cons (vdata) (rest)))) (PreH9 : (safeExec (pre_dfs1 (g_low_level_spec) (vis1_m) (fin_m) (timer_m)) (dfs_finish_from (u) ((edges_of (u) (processed)))) X_low_level_spec )) ,
  (IntArray.full vis1 n vis1_m )
  **  (SllPtrArray.missing_i radj n u head radj_rows_low_level_spec )
  **  (sllseg head cur processed )
  **  ((&((cur)  # "list" ->ₛ "data")) # Int  |-> vdata)
  **  ((&((cur)  # "list" ->ₛ "next")) # Ptr  |-> next_ptr)
  **  (sll next_ptr rest )
  **  (IntArray.full fin n fin_m )
  **  (IntArray.full timer_p 1 (cons (timer_m) ((@nil Z))) )
|--
  “ (vdata < n_pre) ”
.

Definition dfs1_entail_wit_3_split_goal_5 := 
forall (n_pre: Z) (u_pre: Z) (radj_rows_low_level_spec: (@list (@list Z))) (X_low_level_spec: (unit -> (KSt -> Prop))) (g_low_level_spec: AdjGraph) (head: Z) (processed: (@list Z)) (rem: (@list Z)) (vis1_m: (@list Z)) (fin_m: (@list Z)) (timer_m: Z) (vdata: Z) (rest: (@list Z)) (next_ptr: Z) (cur: Z) (n: Z) (u: Z) (radj: Z) (vis1: Z) (fin: Z) (timer_p: Z) (PreH1 : (vdata <= INT_MAX)) (PreH2 : (vdata >= INT_MIN)) (PreH3 : ((Znth vdata vis1_m 0) = 0)) (PreH4 : (cur <> 0)) (PreH5 : (0 <= vdata)) (PreH6 : (vdata < n)) (PreH7 : (n <= INT_MAX)) (PreH8 : (rem = (cons (vdata) (rest)))) (PreH9 : (safeExec (pre_dfs1 (g_low_level_spec) (vis1_m) (fin_m) (timer_m)) (dfs_finish_from (u) ((edges_of (u) (processed)))) X_low_level_spec )) ,
  (IntArray.full vis1 n vis1_m )
  **  (SllPtrArray.missing_i radj n u head radj_rows_low_level_spec )
  **  (sllseg head cur processed )
  **  ((&((cur)  # "list" ->ₛ "data")) # Int  |-> vdata)
  **  ((&((cur)  # "list" ->ₛ "next")) # Ptr  |-> next_ptr)
  **  (sll next_ptr rest )
  **  (IntArray.full fin n fin_m )
  **  (IntArray.full timer_p 1 (cons (timer_m) ((@nil Z))) )
|--
  “ (u_pre < n_pre) ”
.

Definition dfs1_entail_wit_3_split_goal_6 := 
forall (u_pre: Z) (radj_rows_low_level_spec: (@list (@list Z))) (X_low_level_spec: (unit -> (KSt -> Prop))) (g_low_level_spec: AdjGraph) (head: Z) (processed: (@list Z)) (rem: (@list Z)) (vis1_m: (@list Z)) (fin_m: (@list Z)) (timer_m: Z) (vdata: Z) (rest: (@list Z)) (next_ptr: Z) (cur: Z) (n: Z) (u: Z) (radj: Z) (vis1: Z) (fin: Z) (timer_p: Z) (PreH1 : (vdata <= INT_MAX)) (PreH2 : (vdata >= INT_MIN)) (PreH3 : ((Znth vdata vis1_m 0) = 0)) (PreH4 : (cur <> 0)) (PreH5 : (0 <= vdata)) (PreH6 : (vdata < n)) (PreH7 : (n <= INT_MAX)) (PreH8 : (rem = (cons (vdata) (rest)))) (PreH9 : (safeExec (pre_dfs1 (g_low_level_spec) (vis1_m) (fin_m) (timer_m)) (dfs_finish_from (u) ((edges_of (u) (processed)))) X_low_level_spec )) ,
  (IntArray.full vis1 n vis1_m )
  **  (SllPtrArray.missing_i radj n u head radj_rows_low_level_spec )
  **  (sllseg head cur processed )
  **  ((&((cur)  # "list" ->ₛ "data")) # Int  |-> vdata)
  **  ((&((cur)  # "list" ->ₛ "next")) # Ptr  |-> next_ptr)
  **  (sll next_ptr rest )
  **  (IntArray.full fin n fin_m )
  **  (IntArray.full timer_p 1 (cons (timer_m) ((@nil Z))) )
|--
  “ (0 <= u_pre) ”
.

Definition dfs1_entail_wit_3_split_goal_7 := 
forall (n_pre: Z) (radj_rows_low_level_spec: (@list (@list Z))) (X_low_level_spec: (unit -> (KSt -> Prop))) (g_low_level_spec: AdjGraph) (head: Z) (processed: (@list Z)) (rem: (@list Z)) (vis1_m: (@list Z)) (fin_m: (@list Z)) (timer_m: Z) (vdata: Z) (rest: (@list Z)) (next_ptr: Z) (cur: Z) (n: Z) (u: Z) (radj: Z) (vis1: Z) (fin: Z) (timer_p: Z) (PreH1 : (vdata <= INT_MAX)) (PreH2 : (vdata >= INT_MIN)) (PreH3 : ((Znth vdata vis1_m 0) = 0)) (PreH4 : (cur <> 0)) (PreH5 : (0 <= vdata)) (PreH6 : (vdata < n)) (PreH7 : (n <= INT_MAX)) (PreH8 : (rem = (cons (vdata) (rest)))) (PreH9 : (safeExec (pre_dfs1 (g_low_level_spec) (vis1_m) (fin_m) (timer_m)) (dfs_finish_from (u) ((edges_of (u) (processed)))) X_low_level_spec )) ,
  (IntArray.full vis1 n vis1_m )
  **  (SllPtrArray.missing_i radj n u head radj_rows_low_level_spec )
  **  (sllseg head cur processed )
  **  ((&((cur)  # "list" ->ₛ "data")) # Int  |-> vdata)
  **  ((&((cur)  # "list" ->ₛ "next")) # Ptr  |-> next_ptr)
  **  (sll next_ptr rest )
  **  (IntArray.full fin n fin_m )
  **  (IntArray.full timer_p 1 (cons (timer_m) ((@nil Z))) )
|--
  “ (n = n_pre) ”
.

Definition dfs1_entail_wit_3_split_goal_8 := 
forall (u_pre: Z) (radj_rows_low_level_spec: (@list (@list Z))) (X_low_level_spec: (unit -> (KSt -> Prop))) (g_low_level_spec: AdjGraph) (head: Z) (processed: (@list Z)) (rem: (@list Z)) (vis1_m: (@list Z)) (fin_m: (@list Z)) (timer_m: Z) (vdata: Z) (rest: (@list Z)) (next_ptr: Z) (cur: Z) (n: Z) (u: Z) (radj: Z) (vis1: Z) (fin: Z) (timer_p: Z) (PreH1 : (vdata <= INT_MAX)) (PreH2 : (vdata >= INT_MIN)) (PreH3 : ((Znth vdata vis1_m 0) = 0)) (PreH4 : (cur <> 0)) (PreH5 : (0 <= vdata)) (PreH6 : (vdata < n)) (PreH7 : (n <= INT_MAX)) (PreH8 : (rem = (cons (vdata) (rest)))) (PreH9 : (safeExec (pre_dfs1 (g_low_level_spec) (vis1_m) (fin_m) (timer_m)) (dfs_finish_from (u) ((edges_of (u) (processed)))) X_low_level_spec )) ,
  (IntArray.full vis1 n vis1_m )
  **  (SllPtrArray.missing_i radj n u head radj_rows_low_level_spec )
  **  (sllseg head cur processed )
  **  ((&((cur)  # "list" ->ₛ "data")) # Int  |-> vdata)
  **  ((&((cur)  # "list" ->ₛ "next")) # Ptr  |-> next_ptr)
  **  (sll next_ptr rest )
  **  (IntArray.full fin n fin_m )
  **  (IntArray.full timer_p 1 (cons (timer_m) ((@nil Z))) )
|--
  “ (u = u_pre) ”
.

Definition dfs1_entail_wit_3_split_goal_9 := 
forall (radj_pre: Z) (radj_rows_low_level_spec: (@list (@list Z))) (X_low_level_spec: (unit -> (KSt -> Prop))) (g_low_level_spec: AdjGraph) (head: Z) (processed: (@list Z)) (rem: (@list Z)) (vis1_m: (@list Z)) (fin_m: (@list Z)) (timer_m: Z) (vdata: Z) (rest: (@list Z)) (next_ptr: Z) (cur: Z) (n: Z) (u: Z) (radj: Z) (vis1: Z) (fin: Z) (timer_p: Z) (PreH1 : (vdata <= INT_MAX)) (PreH2 : (vdata >= INT_MIN)) (PreH3 : ((Znth vdata vis1_m 0) = 0)) (PreH4 : (cur <> 0)) (PreH5 : (0 <= vdata)) (PreH6 : (vdata < n)) (PreH7 : (n <= INT_MAX)) (PreH8 : (rem = (cons (vdata) (rest)))) (PreH9 : (safeExec (pre_dfs1 (g_low_level_spec) (vis1_m) (fin_m) (timer_m)) (dfs_finish_from (u) ((edges_of (u) (processed)))) X_low_level_spec )) ,
  (IntArray.full vis1 n vis1_m )
  **  (SllPtrArray.missing_i radj n u head radj_rows_low_level_spec )
  **  (sllseg head cur processed )
  **  ((&((cur)  # "list" ->ₛ "data")) # Int  |-> vdata)
  **  ((&((cur)  # "list" ->ₛ "next")) # Ptr  |-> next_ptr)
  **  (sll next_ptr rest )
  **  (IntArray.full fin n fin_m )
  **  (IntArray.full timer_p 1 (cons (timer_m) ((@nil Z))) )
|--
  “ (radj = radj_pre) ”
.

Definition dfs1_entail_wit_3_split_goal_10 := 
forall (vis1_pre: Z) (radj_rows_low_level_spec: (@list (@list Z))) (X_low_level_spec: (unit -> (KSt -> Prop))) (g_low_level_spec: AdjGraph) (head: Z) (processed: (@list Z)) (rem: (@list Z)) (vis1_m: (@list Z)) (fin_m: (@list Z)) (timer_m: Z) (vdata: Z) (rest: (@list Z)) (next_ptr: Z) (cur: Z) (n: Z) (u: Z) (radj: Z) (vis1: Z) (fin: Z) (timer_p: Z) (PreH1 : (vdata <= INT_MAX)) (PreH2 : (vdata >= INT_MIN)) (PreH3 : ((Znth vdata vis1_m 0) = 0)) (PreH4 : (cur <> 0)) (PreH5 : (0 <= vdata)) (PreH6 : (vdata < n)) (PreH7 : (n <= INT_MAX)) (PreH8 : (rem = (cons (vdata) (rest)))) (PreH9 : (safeExec (pre_dfs1 (g_low_level_spec) (vis1_m) (fin_m) (timer_m)) (dfs_finish_from (u) ((edges_of (u) (processed)))) X_low_level_spec )) ,
  (IntArray.full vis1 n vis1_m )
  **  (SllPtrArray.missing_i radj n u head radj_rows_low_level_spec )
  **  (sllseg head cur processed )
  **  ((&((cur)  # "list" ->ₛ "data")) # Int  |-> vdata)
  **  ((&((cur)  # "list" ->ₛ "next")) # Ptr  |-> next_ptr)
  **  (sll next_ptr rest )
  **  (IntArray.full fin n fin_m )
  **  (IntArray.full timer_p 1 (cons (timer_m) ((@nil Z))) )
|--
  “ (vis1 = vis1_pre) ”
.

Definition dfs1_entail_wit_3_split_goal_11 := 
forall (fin_pre: Z) (radj_rows_low_level_spec: (@list (@list Z))) (X_low_level_spec: (unit -> (KSt -> Prop))) (g_low_level_spec: AdjGraph) (head: Z) (processed: (@list Z)) (rem: (@list Z)) (vis1_m: (@list Z)) (fin_m: (@list Z)) (timer_m: Z) (vdata: Z) (rest: (@list Z)) (next_ptr: Z) (cur: Z) (n: Z) (u: Z) (radj: Z) (vis1: Z) (fin: Z) (timer_p: Z) (PreH1 : (vdata <= INT_MAX)) (PreH2 : (vdata >= INT_MIN)) (PreH3 : ((Znth vdata vis1_m 0) = 0)) (PreH4 : (cur <> 0)) (PreH5 : (0 <= vdata)) (PreH6 : (vdata < n)) (PreH7 : (n <= INT_MAX)) (PreH8 : (rem = (cons (vdata) (rest)))) (PreH9 : (safeExec (pre_dfs1 (g_low_level_spec) (vis1_m) (fin_m) (timer_m)) (dfs_finish_from (u) ((edges_of (u) (processed)))) X_low_level_spec )) ,
  (IntArray.full vis1 n vis1_m )
  **  (SllPtrArray.missing_i radj n u head radj_rows_low_level_spec )
  **  (sllseg head cur processed )
  **  ((&((cur)  # "list" ->ₛ "data")) # Int  |-> vdata)
  **  ((&((cur)  # "list" ->ₛ "next")) # Ptr  |-> next_ptr)
  **  (sll next_ptr rest )
  **  (IntArray.full fin n fin_m )
  **  (IntArray.full timer_p 1 (cons (timer_m) ((@nil Z))) )
|--
  “ (fin = fin_pre) ”
.

Definition dfs1_entail_wit_3_split_goal_12 := 
forall (timer_p_pre: Z) (radj_rows_low_level_spec: (@list (@list Z))) (X_low_level_spec: (unit -> (KSt -> Prop))) (g_low_level_spec: AdjGraph) (head: Z) (processed: (@list Z)) (rem: (@list Z)) (vis1_m: (@list Z)) (fin_m: (@list Z)) (timer_m: Z) (vdata: Z) (rest: (@list Z)) (next_ptr: Z) (cur: Z) (n: Z) (u: Z) (radj: Z) (vis1: Z) (fin: Z) (timer_p: Z) (PreH1 : (vdata <= INT_MAX)) (PreH2 : (vdata >= INT_MIN)) (PreH3 : ((Znth vdata vis1_m 0) = 0)) (PreH4 : (cur <> 0)) (PreH5 : (0 <= vdata)) (PreH6 : (vdata < n)) (PreH7 : (n <= INT_MAX)) (PreH8 : (rem = (cons (vdata) (rest)))) (PreH9 : (safeExec (pre_dfs1 (g_low_level_spec) (vis1_m) (fin_m) (timer_m)) (dfs_finish_from (u) ((edges_of (u) (processed)))) X_low_level_spec )) ,
  (IntArray.full vis1 n vis1_m )
  **  (SllPtrArray.missing_i radj n u head radj_rows_low_level_spec )
  **  (sllseg head cur processed )
  **  ((&((cur)  # "list" ->ₛ "data")) # Int  |-> vdata)
  **  ((&((cur)  # "list" ->ₛ "next")) # Ptr  |-> next_ptr)
  **  (sll next_ptr rest )
  **  (IntArray.full fin n fin_m )
  **  (IntArray.full timer_p 1 (cons (timer_m) ((@nil Z))) )
|--
  “ (timer_p = timer_p_pre) ”
.

Definition dfs1_entail_wit_3_split_goal_spatial := 
forall (timer_p_pre: Z) (fin_pre: Z) (vis1_pre: Z) (radj_pre: Z) (n_pre: Z) (radj_rows_low_level_spec: (@list (@list Z))) (X_low_level_spec: (unit -> (KSt -> Prop))) (g_low_level_spec: AdjGraph) (head: Z) (processed: (@list Z)) (rem: (@list Z)) (vis1_m: (@list Z)) (fin_m: (@list Z)) (timer_m: Z) (vdata: Z) (rest: (@list Z)) (next_ptr: Z) (cur: Z) (n: Z) (u: Z) (radj: Z) (vis1: Z) (fin: Z) (timer_p: Z) (PreH1 : (vdata <= INT_MAX)) (PreH2 : (vdata >= INT_MIN)) (PreH3 : ((Znth vdata vis1_m 0) = 0)) (PreH4 : (cur <> 0)) (PreH5 : (0 <= vdata)) (PreH6 : (vdata < n)) (PreH7 : (n <= INT_MAX)) (PreH8 : (rem = (cons (vdata) (rest)))) (PreH9 : (safeExec (pre_dfs1 (g_low_level_spec) (vis1_m) (fin_m) (timer_m)) (dfs_finish_from (u) ((edges_of (u) (processed)))) X_low_level_spec )) ,
  (IntArray.full vis1 n vis1_m )
  **  (SllPtrArray.missing_i radj n u head radj_rows_low_level_spec )
  **  (sllseg head cur processed )
  **  ((&((cur)  # "list" ->ₛ "data")) # Int  |-> vdata)
  **  ((&((cur)  # "list" ->ₛ "next")) # Ptr  |-> next_ptr)
  **  (sll next_ptr rest )
  **  (IntArray.full fin n fin_m )
  **  (IntArray.full timer_p 1 (cons (timer_m) ((@nil Z))) )
|--
  (SllPtrArray.full radj_pre n_pre radj_rows_low_level_spec )
  **  (IntArray.full vis1_pre n_pre vis1_m )
  **  (IntArray.full fin_pre n_pre fin_m )
  **  (IntArray.full timer_p_pre 1 (cons (timer_m) ((@nil Z))) )
.

Definition dfs1_entail_wit_4_1 := 
(
forall (timer_p_pre: Z) (fin_pre: Z) (vis1_pre: Z) (radj_pre: Z) (n_pre: Z) (u_pre: Z) (radj_rows_low_level_spec: (@list (@list Z))) (X_low_level_spec: (unit -> (KSt -> Prop))) (g_low_level_spec: AdjGraph) (head: Z) (processed: (@list Z)) (rem: (@list Z)) (vis1_m: (@list Z)) (fin_m: (@list Z)) (timer_m: Z) (vdata: Z) (rest: (@list Z)) (next_ptr: Z) (cur: Z) (n: Z) (u: Z) (radj: Z) (vis1: Z) (fin: Z) (timer_p: Z) (PreH1 : ((Znth vdata vis1_m 0) <> 0)) (PreH2 : (cur <> 0)) (PreH3 : (0 <= vdata)) (PreH4 : (vdata < n)) (PreH5 : (n <= INT_MAX)) (PreH6 : (rem = (cons (vdata) (rest)))) (PreH7 : (safeExec (pre_dfs1 (g_low_level_spec) (vis1_m) (fin_m) (timer_m)) (dfs_finish_from (u) ((edges_of (u) (processed)))) X_low_level_spec )) ,
  (IntArray.full vis1 n vis1_m )
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "u" ) )) # Int  |-> u)
  **  ((( &( "radj" ) )) # Ptr  |-> radj)
  **  (SllPtrArray.missing_i radj n u head radj_rows_low_level_spec )
  **  (sllseg head cur processed )
  **  ((&((cur)  # "list" ->ₛ "data")) # Int  |-> vdata)
  **  ((&((cur)  # "list" ->ₛ "next")) # Ptr  |-> next_ptr)
  **  (sll next_ptr rest )
  **  ((( &( "vis1" ) )) # Ptr  |-> vis1)
  **  ((( &( "fin" ) )) # Ptr  |-> fin)
  **  (IntArray.full fin n fin_m )
  **  ((( &( "timer_p" ) )) # Ptr  |-> timer_p)
  **  (IntArray.full timer_p 1 (cons (timer_m) ((@nil Z))) )
|--
  EX (next_ptr_: Z)  (vis1_m_: (@list Z))  (fin_m_: (@list Z))  (timer_m_: Z)  (rest_: (@list Z)) ,
  “ (cur <> 0) ” 
  &&  “ (0 <= u_pre) ” 
  &&  “ (u_pre < n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (rem = (cons (vdata) (rest_))) ” 
  &&  “ (safeExec (pre_dfs1 (g_low_level_spec) (vis1_m_) (fin_m_) (timer_m_)) (dfs_finish_from (u_pre) ((edges_of (u_pre) (processed)))) X_low_level_spec ) ”
  &&  ((( &( "u" ) )) # Int  |-> u_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "radj" ) )) # Ptr  |-> radj_pre)
  **  ((( &( "vis1" ) )) # Ptr  |-> vis1_pre)
  **  ((( &( "fin" ) )) # Ptr  |-> fin_pre)
  **  ((( &( "timer_p" ) )) # Ptr  |-> timer_p_pre)
  **  (SllPtrArray.missing_i radj_pre n_pre u_pre head radj_rows_low_level_spec )
  **  (sllseg head cur processed )
  **  ((&((cur)  # "list" ->ₛ "data")) # Int  |-> vdata)
  **  ((&((cur)  # "list" ->ₛ "next")) # Ptr  |-> next_ptr_)
  **  (sll next_ptr_ rest_ )
  **  (IntArray.full vis1_pre n_pre vis1_m_ )
  **  (IntArray.full fin_pre n_pre fin_m_ )
  **  (IntArray.full timer_p_pre 1 (cons (timer_m_) ((@nil Z))) )
) \/
(
forall (timer_p_pre: Z) (fin_pre: Z) (vis1_pre: Z) (radj_pre: Z) (n_pre: Z) (u_pre: Z) (radj_rows_low_level_spec: (@list (@list Z))) (X_low_level_spec: (unit -> (KSt -> Prop))) (g_low_level_spec: AdjGraph) (head: Z) (processed: (@list Z)) (rem: (@list Z)) (vis1_m: (@list Z)) (fin_m: (@list Z)) (timer_m: Z) (vdata: Z) (rest: (@list Z)) (cur: Z) (n: Z) (u: Z) (radj: Z) (vis1: Z) (fin: Z) (timer_p: Z) (PreH1 : ((Znth vdata vis1_m 0) <> 0)) (PreH2 : (cur <> 0)) (PreH3 : (0 <= vdata)) (PreH4 : (vdata < n)) (PreH5 : (n <= INT_MAX)) (PreH6 : (rem = (cons (vdata) (rest)))) (PreH7 : (safeExec (pre_dfs1 (g_low_level_spec) (vis1_m) (fin_m) (timer_m)) (dfs_finish_from (u) ((edges_of (u) (processed)))) X_low_level_spec )) ,
  (IntArray.full vis1 n vis1_m )
  **  (SllPtrArray.missing_i radj n u head radj_rows_low_level_spec )
  **  (sllseg head cur processed )
  **  (IntArray.full fin n fin_m )
  **  (IntArray.full timer_p 1 (cons (timer_m) ((@nil Z))) )
|--
  EX (vis1_m_: (@list Z))  (fin_m_: (@list Z))  (timer_m_: Z) ,
  “ (timer_p = timer_p_pre) ” 
  &&  “ (fin = fin_pre) ” 
  &&  “ (vis1 = vis1_pre) ” 
  &&  “ (radj = radj_pre) ” 
  &&  “ (u = u_pre) ” 
  &&  “ (n = n_pre) ” 
  &&  “ (cur <> 0) ” 
  &&  “ (0 <= u_pre) ” 
  &&  “ (u_pre < n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (rem = (cons (vdata) (rest))) ” 
  &&  “ (safeExec (pre_dfs1 (g_low_level_spec) (vis1_m_) (fin_m_) (timer_m_)) (dfs_finish_from (u_pre) ((edges_of (u_pre) (processed)))) X_low_level_spec ) ”
  &&  (SllPtrArray.missing_i radj_pre n_pre u_pre head radj_rows_low_level_spec )
  **  (sllseg head cur processed )
  **  (IntArray.full vis1_pre n_pre vis1_m_ )
  **  (IntArray.full fin_pre n_pre fin_m_ )
  **  (IntArray.full timer_p_pre 1 (cons (timer_m_) ((@nil Z))) )
).

Definition dfs1_entail_wit_4_2 := 
(
forall (timer_p_pre: Z) (fin_pre: Z) (vis1_pre: Z) (radj_pre: Z) (n_pre: Z) (u_pre: Z) (radj_rows_low_level_spec: (@list (@list Z))) (X_low_level_spec: (unit -> (KSt -> Prop))) (g_low_level_spec: AdjGraph) (head: Z) (processed: (@list Z)) (rem: (@list Z)) (vis1_m: (@list Z)) (cur: Z) (v: Z) (vis1_l_: (@list Z)) (fin_l_: (@list Z)) (timer_v_: Z) (PreH1 : (safeExec (pre_dfs1 (g_low_level_spec) (vis1_l_) (fin_l_) (timer_v_)) (return (tt)) X_low_level_spec )) (PreH2 : (cur <> 0)) (PreH3 : (0 <= u_pre)) (PreH4 : (u_pre < n_pre)) (PreH5 : (0 <= v)) (PreH6 : (v < n_pre)) (PreH7 : (n_pre <= INT_MAX)) (PreH8 : ((Znth (v) (vis1_m) (0)) = 0)) ,
  (SllPtrArray.full radj_pre n_pre radj_rows_low_level_spec )
  **  (IntArray.full vis1_pre n_pre vis1_l_ )
  **  (IntArray.full fin_pre n_pre fin_l_ )
  **  (IntArray.full timer_p_pre 1 (cons (timer_v_) ((@nil Z))) )
|--
  EX (next_ptr_: Z)  (vis1_m_: (@list Z))  (fin_m_: (@list Z))  (timer_m_: Z)  (rest_: (@list Z)) ,
  “ (cur <> 0) ” 
  &&  “ (0 <= u_pre) ” 
  &&  “ (u_pre < n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (rem = (cons (v) (rest_))) ” 
  &&  “ (safeExec (pre_dfs1 (g_low_level_spec) (vis1_m_) (fin_m_) (timer_m_)) (dfs_finish_from (u_pre) ((edges_of (u_pre) (processed)))) X_low_level_spec ) ”
  &&  (SllPtrArray.missing_i radj_pre n_pre u_pre head radj_rows_low_level_spec )
  **  (sllseg head cur processed )
  **  ((&((cur)  # "list" ->ₛ "data")) # Int  |-> v)
  **  ((&((cur)  # "list" ->ₛ "next")) # Ptr  |-> next_ptr_)
  **  (sll next_ptr_ rest_ )
  **  (IntArray.full vis1_pre n_pre vis1_m_ )
  **  (IntArray.full fin_pre n_pre fin_m_ )
  **  (IntArray.full timer_p_pre 1 (cons (timer_m_) ((@nil Z))) )
) \/
(
forall (radj_pre: Z) (n_pre: Z) (u_pre: Z) (radj_rows_low_level_spec: (@list (@list Z))) (X_low_level_spec: (unit -> (KSt -> Prop))) (g_low_level_spec: AdjGraph) (head: Z) (processed: (@list Z)) (rem: (@list Z)) (vis1_m: (@list Z)) (cur: Z) (v: Z) (vis1_l_: (@list Z)) (fin_l_: (@list Z)) (timer_v_: Z) (PreH1 : (safeExec (pre_dfs1 (g_low_level_spec) (vis1_l_) (fin_l_) (timer_v_)) (return (tt)) X_low_level_spec )) (PreH2 : (cur <> 0)) (PreH3 : (0 <= u_pre)) (PreH4 : (u_pre < n_pre)) (PreH5 : (0 <= v)) (PreH6 : (v < n_pre)) (PreH7 : (n_pre <= INT_MAX)) (PreH8 : ((Znth (v) (vis1_m) (0)) = 0)) ,
  (SllPtrArray.full radj_pre n_pre radj_rows_low_level_spec )
|--
  EX (next_ptr_: Z)  (timer_m_: Z)  (rest_: (@list Z)) ,
  “ ((cons (timer_v_) ((@nil Z))) = (cons (timer_m_) ((@nil Z)))) ” 
  &&  “ (cur <> 0) ” 
  &&  “ (0 <= u_pre) ” 
  &&  “ (u_pre < n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (rem = (cons (v) (rest_))) ” 
  &&  “ (safeExec (pre_dfs1 (g_low_level_spec) (vis1_l_) (fin_l_) (timer_m_)) (dfs_finish_from (u_pre) ((edges_of (u_pre) (processed)))) X_low_level_spec ) ”
  &&  (SllPtrArray.missing_i radj_pre n_pre u_pre head radj_rows_low_level_spec )
  **  (sllseg head cur processed )
  **  ((&((cur)  # "list" ->ₛ "data")) # Int  |-> v)
  **  ((&((cur)  # "list" ->ₛ "next")) # Ptr  |-> next_ptr_)
  **  (sll next_ptr_ rest_ )
).

Definition dfs1_entail_wit_5 := 
(
forall (timer_p_pre: Z) (fin_pre: Z) (vis1_pre: Z) (radj_pre: Z) (n_pre: Z) (u_pre: Z) (radj_rows_low_level_spec: (@list (@list Z))) (X_low_level_spec: (unit -> (KSt -> Prop))) (g_low_level_spec: AdjGraph) (head_2: Z) (processed_2: (@list Z)) (rem_2: (@list Z)) (vdata_: Z) (rest_: (@list Z)) (next_ptr_: Z) (vis1_m_: (@list Z)) (fin_m_: (@list Z)) (timer_m_: Z) (cur: Z) (PreH1 : (cur <> 0)) (PreH2 : (0 <= u_pre)) (PreH3 : (u_pre < n_pre)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : (rem_2 = (cons (vdata_) (rest_)))) (PreH6 : (safeExec (pre_dfs1 (g_low_level_spec) (vis1_m_) (fin_m_) (timer_m_)) (dfs_finish_from (u_pre) ((edges_of (u_pre) (processed_2)))) X_low_level_spec )) ,
  (SllPtrArray.missing_i radj_pre n_pre u_pre head_2 radj_rows_low_level_spec )
  **  (sllseg head_2 cur processed_2 )
  **  ((&((cur)  # "list" ->ₛ "data")) # Int  |-> vdata_)
  **  ((&((cur)  # "list" ->ₛ "next")) # Ptr  |-> next_ptr_)
  **  (sll next_ptr_ rest_ )
  **  (IntArray.full vis1_pre n_pre vis1_m_ )
  **  (IntArray.full fin_pre n_pre fin_m_ )
  **  (IntArray.full timer_p_pre 1 (cons (timer_m_) ((@nil Z))) )
|--
  EX (rem: (@list Z))  (head: Z)  (vis1_m: (@list Z))  (fin_m: (@list Z))  (timer_m: Z)  (processed: (@list Z)) ,
  “ (safeExec (pre_dfs1 (g_low_level_spec) (vis1_m) (fin_m) (timer_m)) (dfs_finish_from (u_pre) ((edges_of (u_pre) (processed)))) X_low_level_spec ) ” 
  &&  “ (0 <= u_pre) ” 
  &&  “ (u_pre < n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ”
  &&  (SllPtrArray.missing_i radj_pre n_pre u_pre head radj_rows_low_level_spec )
  **  (sllseg head next_ptr_ processed )
  **  (sll next_ptr_ rem )
  **  (IntArray.full vis1_pre n_pre vis1_m )
  **  (IntArray.full fin_pre n_pre fin_m )
  **  (IntArray.full timer_p_pre 1 (cons (timer_m) ((@nil Z))) )
) \/
(
forall (radj_pre: Z) (n_pre: Z) (u_pre: Z) (radj_rows_low_level_spec: (@list (@list Z))) (X_low_level_spec: (unit -> (KSt -> Prop))) (g_low_level_spec: AdjGraph) (head_2: Z) (processed_2: (@list Z)) (rem_2: (@list Z)) (vdata_: Z) (rest_: (@list Z)) (next_ptr_: Z) (vis1_m_: (@list Z)) (fin_m_: (@list Z)) (timer_m_: Z) (cur: Z) (PreH1 : (vdata_ <= INT_MAX)) (PreH2 : (vdata_ >= INT_MIN)) (PreH3 : (cur <> 0)) (PreH4 : (0 <= u_pre)) (PreH5 : (u_pre < n_pre)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : (rem_2 = (cons (vdata_) (rest_)))) (PreH8 : (safeExec (pre_dfs1 (g_low_level_spec) (vis1_m_) (fin_m_) (timer_m_)) (dfs_finish_from (u_pre) ((edges_of (u_pre) (processed_2)))) X_low_level_spec )) ,
  (SllPtrArray.missing_i radj_pre n_pre u_pre head_2 radj_rows_low_level_spec )
  **  (sllseg head_2 cur processed_2 )
  **  ((&((cur)  # "list" ->ₛ "data")) # Int  |-> vdata_)
  **  ((&((cur)  # "list" ->ₛ "next")) # Ptr  |-> next_ptr_)
|--
  EX (head: Z)  (timer_m: Z)  (processed: (@list Z)) ,
  “ ((cons (timer_m_) ((@nil Z))) = (cons (timer_m) ((@nil Z)))) ” 
  &&  “ (safeExec (pre_dfs1 (g_low_level_spec) (vis1_m_) (fin_m_) (timer_m)) (dfs_finish_from (u_pre) ((edges_of (u_pre) (processed)))) X_low_level_spec ) ” 
  &&  “ (0 <= u_pre) ” 
  &&  “ (u_pre < n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ”
  &&  (SllPtrArray.missing_i radj_pre n_pre u_pre head radj_rows_low_level_spec )
  **  (sllseg head next_ptr_ processed )
).

Definition dfs1_entail_wit_6 := 
(
forall (timer_p_pre: Z) (fin_pre: Z) (vis1_pre: Z) (radj_pre: Z) (n_pre: Z) (u_pre: Z) (radj_rows_low_level_spec: (@list (@list Z))) (X_low_level_spec: (unit -> (KSt -> Prop))) (g_low_level_spec: AdjGraph) (rem: (@list Z)) (cur: Z) (head_2: Z) (vis1_m_2: (@list Z)) (fin_m_2: (@list Z)) (timer_m: Z) (processed: (@list Z)) (PreH1 : (cur = 0)) (PreH2 : (safeExec (pre_dfs1 (g_low_level_spec) (vis1_m_2) (fin_m_2) (timer_m)) (dfs_finish_from (u_pre) ((edges_of (u_pre) (processed)))) X_low_level_spec )) (PreH3 : (0 <= u_pre)) (PreH4 : (u_pre < n_pre)) (PreH5 : (n_pre <= INT_MAX)) ,
  (IntArray.full timer_p_pre 1 (cons (timer_m) ((@nil Z))) )
  **  (SllPtrArray.missing_i radj_pre n_pre u_pre head_2 radj_rows_low_level_spec )
  **  ((( &( "cur" ) )) # Ptr  |-> cur)
  **  (sllseg head_2 cur processed )
  **  (sll cur rem )
  **  (IntArray.full vis1_pre n_pre vis1_m_2 )
  **  (IntArray.full fin_pre n_pre fin_m_2 )
|--
  EX (head: Z)  (vis1_m: (@list Z))  (timer_m_set: Z)  (fin_m: (@list Z))  (fin_m_set: (@list Z)) ,
  “ (0 <= u_pre) ” 
  &&  “ (u_pre < n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (fin_m_set = (replace_Znth (u_pre) ((Znth 0 (cons (timer_m) ((@nil Z))) 0)) (fin_m))) ” 
  &&  “ (timer_m_set = ((Znth 0 (cons (timer_m) ((@nil Z))) 0) + 1 )) ” 
  &&  “ (safeExec (pre_dfs1 (g_low_level_spec) (vis1_m) (fin_m_set) (timer_m_set)) (return (tt)) X_low_level_spec ) ”
  &&  (SllPtrArray.missing_i radj_pre n_pre u_pre head radj_rows_low_level_spec )
  **  (sll head (Znth (u_pre) (radj_rows_low_level_spec) ((@nil Z))) )
  **  ((( &( "cur" ) )) # Ptr  |-> 0)
  **  (IntArray.full vis1_pre n_pre vis1_m )
  **  (IntArray.full fin_pre n_pre fin_m_set )
  **  (IntArray.full timer_p_pre 1 (cons ((Znth 0 (cons (timer_m) ((@nil Z))) 0)) ((@nil Z))) )
) \/
(
forall (radj_pre: Z) (n_pre: Z) (u_pre: Z) (radj_rows_low_level_spec: (@list (@list Z))) (X_low_level_spec: (unit -> (KSt -> Prop))) (g_low_level_spec: AdjGraph) (rem: (@list Z)) (cur: Z) (head_2: Z) (vis1_m_2: (@list Z)) (fin_m_2: (@list Z)) (timer_m: Z) (processed: (@list Z)) (PreH1 : (cur = 0)) (PreH2 : (safeExec (pre_dfs1 (g_low_level_spec) (vis1_m_2) (fin_m_2) (timer_m)) (dfs_finish_from (u_pre) ((edges_of (u_pre) (processed)))) X_low_level_spec )) (PreH3 : (0 <= u_pre)) (PreH4 : (u_pre < n_pre)) (PreH5 : (n_pre <= INT_MAX)) ,
  (SllPtrArray.missing_i radj_pre n_pre u_pre head_2 radj_rows_low_level_spec )
  **  (sllseg head_2 cur processed )
  **  (sll cur rem )
|--
  EX (head: Z)  (fin_m: (@list Z)) ,
  “ (fin_m_2 = (replace_Znth (u_pre) ((Znth 0 (cons (timer_m) ((@nil Z))) 0)) (fin_m))) ” 
  &&  “ ((cons (timer_m) ((@nil Z))) = (cons ((Znth 0 (cons (timer_m) ((@nil Z))) 0)) ((@nil Z)))) ” 
  &&  “ (cur = 0) ” 
  &&  “ (0 <= u_pre) ” 
  &&  “ (u_pre < n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (safeExec (pre_dfs1 (g_low_level_spec) (vis1_m_2) ((replace_Znth (u_pre) ((Znth 0 (cons (timer_m) ((@nil Z))) 0)) (fin_m))) (((Znth 0 (cons (timer_m) ((@nil Z))) 0) + 1 ))) (return (tt)) X_low_level_spec ) ”
  &&  (SllPtrArray.missing_i radj_pre n_pre u_pre head radj_rows_low_level_spec )
  **  (sll head (Znth (u_pre) (radj_rows_low_level_spec) ((@nil Z))) )
).

Definition dfs1_return_wit_1 := 
(
forall (timer_p_pre: Z) (fin_pre: Z) (vis1_pre: Z) (radj_pre: Z) (n_pre: Z) (u_pre: Z) (radj_rows_low_level_spec: (@list (@list Z))) (X_low_level_spec: (unit -> (KSt -> Prop))) (g_low_level_spec: AdjGraph) (head: Z) (vis1_m: (@list Z)) (fin_m: (@list Z)) (timer_m: Z) (fin_m_set: (@list Z)) (timer_m_set: Z) (PreH1 : (0 <= u_pre)) (PreH2 : (u_pre < n_pre)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (fin_m_set = (replace_Znth (u_pre) (timer_m) (fin_m)))) (PreH5 : (timer_m_set = (timer_m + 1 ))) (PreH6 : (safeExec (pre_dfs1 (g_low_level_spec) (vis1_m) (fin_m_set) (timer_m_set)) (return (tt)) X_low_level_spec )) ,
  (IntArray.full timer_p_pre 1 (replace_Znth (0) ((timer_m + 1 )) ((cons (timer_m) ((@nil Z))))) )
  **  (IntArray.full fin_pre n_pre (replace_Znth (u_pre) (timer_m) (fin_m_set)) )
  **  (SllPtrArray.missing_i radj_pre n_pre u_pre head radj_rows_low_level_spec )
  **  (sll head (Znth (u_pre) (radj_rows_low_level_spec) ((@nil Z))) )
  **  (IntArray.full vis1_pre n_pre vis1_m )
|--
  EX (vis1_l_: (@list Z))  (fin_l_: (@list Z))  (timer_v_: Z) ,
  “ (safeExec (pre_dfs1 (g_low_level_spec) (vis1_l_) (fin_l_) (timer_v_)) (return (tt)) X_low_level_spec ) ”
  &&  (SllPtrArray.full radj_pre n_pre radj_rows_low_level_spec )
  **  (IntArray.full vis1_pre n_pre vis1_l_ )
  **  (IntArray.full fin_pre n_pre fin_l_ )
  **  (IntArray.full timer_p_pre 1 (cons (timer_v_) ((@nil Z))) )
) \/
(
forall (radj_pre: Z) (n_pre: Z) (u_pre: Z) (radj_rows_low_level_spec: (@list (@list Z))) (X_low_level_spec: (unit -> (KSt -> Prop))) (g_low_level_spec: AdjGraph) (head: Z) (vis1_m: (@list Z)) (fin_m: (@list Z)) (timer_m: Z) (fin_m_set: (@list Z)) (timer_m_set: Z) (PreH1 : (0 <= u_pre)) (PreH2 : (u_pre < n_pre)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (fin_m_set = (replace_Znth (u_pre) (timer_m) (fin_m)))) (PreH5 : (timer_m_set = (timer_m + 1 ))) (PreH6 : (safeExec (pre_dfs1 (g_low_level_spec) (vis1_m) (fin_m_set) (timer_m_set)) (return (tt)) X_low_level_spec )) ,
  (SllPtrArray.missing_i radj_pre n_pre u_pre head radj_rows_low_level_spec )
  **  (sll head (Znth (u_pre) (radj_rows_low_level_spec) ((@nil Z))) )
|--
  EX (timer_v_: Z) ,
  “ ((replace_Znth (0) ((timer_m + 1 )) ((cons (timer_m) ((@nil Z))))) = (cons (timer_v_) ((@nil Z)))) ” 
  &&  “ (safeExec (pre_dfs1 (g_low_level_spec) (vis1_m) ((replace_Znth (u_pre) (timer_m) (fin_m_set))) (timer_v_)) (return (tt)) X_low_level_spec ) ”
  &&  (SllPtrArray.full radj_pre n_pre radj_rows_low_level_spec )
).

Definition dfs1_partial_solve_wit_1 := 
forall (timer_p_pre: Z) (fin_pre: Z) (vis1_pre: Z) (radj_pre: Z) (n_pre: Z) (u_pre: Z) (radj_rows_low_level_spec: (@list (@list Z))) (X_low_level_spec: (unit -> (KSt -> Prop))) (timer_v_low_level_spec: Z) (fin_l_low_level_spec: (@list Z)) (vis1_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (PreH1 : (safeExec (pre_dfs1 (g_low_level_spec) (vis1_l_low_level_spec) (fin_l_low_level_spec) (timer_v_low_level_spec)) (dfs_finish (u_pre)) X_low_level_spec )) (PreH2 : (0 <= u_pre)) (PreH3 : (u_pre < n_pre)) (PreH4 : (n_pre <= INT_MAX)) ,
  (SllPtrArray.full radj_pre n_pre radj_rows_low_level_spec )
  **  (IntArray.full vis1_pre n_pre vis1_l_low_level_spec )
  **  (IntArray.full fin_pre n_pre fin_l_low_level_spec )
  **  (IntArray.full timer_p_pre 1 (cons (timer_v_low_level_spec) ((@nil Z))) )
|--
  “ (safeExec (pre_dfs1 (g_low_level_spec) (vis1_l_low_level_spec) (fin_l_low_level_spec) (timer_v_low_level_spec)) (dfs_finish (u_pre)) X_low_level_spec ) ” 
  &&  “ (0 <= u_pre) ” 
  &&  “ (u_pre < n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ”
  &&  (((vis1_pre + (u_pre * sizeof(INT) ) )) # Int  |->_)
  **  (IntArray.missing_i vis1_pre u_pre 0 n_pre vis1_l_low_level_spec )
  **  (SllPtrArray.full radj_pre n_pre radj_rows_low_level_spec )
  **  (IntArray.full fin_pre n_pre fin_l_low_level_spec )
  **  (IntArray.full timer_p_pre 1 (cons (timer_v_low_level_spec) ((@nil Z))) )
.

Definition dfs1_partial_solve_wit_2 := 
forall (timer_p_pre: Z) (fin_pre: Z) (vis1_pre: Z) (radj_pre: Z) (n_pre: Z) (u_pre: Z) (radj_rows_low_level_spec: (@list (@list Z))) (X_low_level_spec: (unit -> (KSt -> Prop))) (timer_v_low_level_spec: Z) (fin_l_low_level_spec: (@list Z)) (vis1_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph)  __default__List_Z (PreH1 : (safeExec (pre_dfs1 (g_low_level_spec) (vis1_l_low_level_spec) (fin_l_low_level_spec) (timer_v_low_level_spec)) (dfs_finish (u_pre)) X_low_level_spec )) (PreH2 : (0 <= u_pre)) (PreH3 : (u_pre < n_pre)) (PreH4 : (n_pre <= INT_MAX)) ,
  (IntArray.full vis1_pre n_pre (replace_Znth (u_pre) (1) (vis1_l_low_level_spec)) )
  **  (SllPtrArray.full radj_pre n_pre radj_rows_low_level_spec )
  **  (IntArray.full fin_pre n_pre fin_l_low_level_spec )
  **  (IntArray.full timer_p_pre 1 (cons (timer_v_low_level_spec) ((@nil Z))) )
|--
  EX (row_ptr: Z) ,
  “ (safeExec (pre_dfs1 (g_low_level_spec) (vis1_l_low_level_spec) (fin_l_low_level_spec) (timer_v_low_level_spec)) (dfs_finish (u_pre)) X_low_level_spec ) ” 
  &&  “ (0 <= u_pre) ” 
  &&  “ (u_pre < n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ”
  &&  (((radj_pre + (u_pre * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (sll row_ptr (Znth u_pre radj_rows_low_level_spec __default__List_Z) )
  **  (SllPtrArray.missing_i radj_pre n_pre u_pre row_ptr radj_rows_low_level_spec )
  **  (IntArray.full vis1_pre n_pre (replace_Znth (u_pre) (1) (vis1_l_low_level_spec)) )
  **  (IntArray.full fin_pre n_pre fin_l_low_level_spec )
  **  (IntArray.full timer_p_pre 1 (cons (timer_v_low_level_spec) ((@nil Z))) )
.

Definition dfs1_partial_solve_wit_3 := 
forall (radj_rows_low_level_spec: (@list (@list Z))) (X_low_level_spec: (unit -> (KSt -> Prop))) (g_low_level_spec: AdjGraph) (head: Z) (processed: (@list Z)) (rem: (@list Z)) (vis1_m: (@list Z)) (fin_m: (@list Z)) (timer_m: Z) (vdata: Z) (rest: (@list Z)) (next_ptr: Z) (cur: Z) (n: Z) (u: Z) (radj: Z) (vis1: Z) (fin: Z) (timer_p: Z) (PreH1 : (cur <> 0)) (PreH2 : (0 <= vdata)) (PreH3 : (vdata < n)) (PreH4 : (n <= INT_MAX)) (PreH5 : (rem = (cons (vdata) (rest)))) (PreH6 : (safeExec (pre_dfs1 (g_low_level_spec) (vis1_m) (fin_m) (timer_m)) (dfs_finish_from (u) ((edges_of (u) (processed)))) X_low_level_spec )) ,
  (SllPtrArray.missing_i radj n u head radj_rows_low_level_spec )
  **  (sllseg head cur processed )
  **  ((&((cur)  # "list" ->ₛ "data")) # Int  |-> vdata)
  **  ((&((cur)  # "list" ->ₛ "next")) # Ptr  |-> next_ptr)
  **  (sll next_ptr rest )
  **  (IntArray.full vis1 n vis1_m )
  **  (IntArray.full fin n fin_m )
  **  (IntArray.full timer_p 1 (cons (timer_m) ((@nil Z))) )
|--
  “ (cur <> 0) ” 
  &&  “ (0 <= vdata) ” 
  &&  “ (vdata < n) ” 
  &&  “ (n <= INT_MAX) ” 
  &&  “ (rem = (cons (vdata) (rest))) ” 
  &&  “ (safeExec (pre_dfs1 (g_low_level_spec) (vis1_m) (fin_m) (timer_m)) (dfs_finish_from (u) ((edges_of (u) (processed)))) X_low_level_spec ) ”
  &&  (((vis1 + (vdata * sizeof(INT) ) )) # Int  |-> (Znth vdata vis1_m 0))
  **  (IntArray.missing_i vis1 vdata 0 n vis1_m )
  **  (SllPtrArray.missing_i radj n u head radj_rows_low_level_spec )
  **  (sllseg head cur processed )
  **  ((&((cur)  # "list" ->ₛ "data")) # Int  |-> vdata)
  **  ((&((cur)  # "list" ->ₛ "next")) # Ptr  |-> next_ptr)
  **  (sll next_ptr rest )
  **  (IntArray.full fin n fin_m )
  **  (IntArray.full timer_p 1 (cons (timer_m) ((@nil Z))) )
.

Definition dfs1_partial_solve_wit_4_pure := 
forall (timer_p_pre: Z) (fin_pre: Z) (vis1_pre: Z) (radj_pre: Z) (n_pre: Z) (u_pre: Z) (radj_rows_low_level_spec: (@list (@list Z))) (X_low_level_spec: (unit -> (KSt -> Prop))) (g_low_level_spec: AdjGraph) (vis1_m: (@list Z)) (fin_m: (@list Z)) (timer_m: Z) (cur: Z) (v: Z) (PreH1 : (cur <> 0)) (PreH2 : (0 <= u_pre)) (PreH3 : (u_pre < n_pre)) (PreH4 : (0 <= v)) (PreH5 : (v < n_pre)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : ((Znth (v) (vis1_m) (0)) = 0)) (PreH8 : (safeExec (pre_dfs1 (g_low_level_spec) (vis1_m) (fin_m) (timer_m)) (dfs_finish (v)) X_low_level_spec )) ,
  ((( &( "u" ) )) # Int  |-> u_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "radj" ) )) # Ptr  |-> radj_pre)
  **  ((( &( "vis1" ) )) # Ptr  |-> vis1_pre)
  **  ((( &( "fin" ) )) # Ptr  |-> fin_pre)
  **  ((( &( "timer_p" ) )) # Ptr  |-> timer_p_pre)
  **  ((( &( "cur" ) )) # Ptr  |-> cur)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  (SllPtrArray.full radj_pre n_pre radj_rows_low_level_spec )
  **  (IntArray.full vis1_pre n_pre vis1_m )
  **  (IntArray.full fin_pre n_pre fin_m )
  **  (IntArray.full timer_p_pre 1 (cons (timer_m) ((@nil Z))) )
|--
  “ (safeExec (pre_dfs1 (g_low_level_spec) (vis1_m) (fin_m) (timer_m)) (dfs_finish (v)) X_low_level_spec ) ” 
  &&  “ (0 <= v) ” 
  &&  “ (v < n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ”
.

Definition dfs1_partial_solve_wit_4_aux := 
forall (timer_p_pre: Z) (fin_pre: Z) (vis1_pre: Z) (radj_pre: Z) (n_pre: Z) (u_pre: Z) (radj_rows_low_level_spec: (@list (@list Z))) (X_low_level_spec: (unit -> (KSt -> Prop))) (g_low_level_spec: AdjGraph) (vis1_m: (@list Z)) (fin_m: (@list Z)) (timer_m: Z) (cur: Z) (v: Z) (PreH1 : (cur <> 0)) (PreH2 : (0 <= u_pre)) (PreH3 : (u_pre < n_pre)) (PreH4 : (0 <= v)) (PreH5 : (v < n_pre)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : ((Znth (v) (vis1_m) (0)) = 0)) (PreH8 : (safeExec (pre_dfs1 (g_low_level_spec) (vis1_m) (fin_m) (timer_m)) (dfs_finish (v)) X_low_level_spec )) ,
  (SllPtrArray.full radj_pre n_pre radj_rows_low_level_spec )
  **  (IntArray.full vis1_pre n_pre vis1_m )
  **  (IntArray.full fin_pre n_pre fin_m )
  **  (IntArray.full timer_p_pre 1 (cons (timer_m) ((@nil Z))) )
|--
  “ (safeExec (pre_dfs1 (g_low_level_spec) (vis1_m) (fin_m) (timer_m)) (dfs_finish (v)) X_low_level_spec ) ” 
  &&  “ (0 <= v) ” 
  &&  “ (v < n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (cur <> 0) ” 
  &&  “ (0 <= u_pre) ” 
  &&  “ (u_pre < n_pre) ” 
  &&  “ (0 <= v) ” 
  &&  “ (v < n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ ((Znth (v) (vis1_m) (0)) = 0) ” 
  &&  “ (safeExec (pre_dfs1 (g_low_level_spec) (vis1_m) (fin_m) (timer_m)) (dfs_finish (v)) X_low_level_spec ) ”
  &&  (SllPtrArray.full radj_pre n_pre radj_rows_low_level_spec )
  **  (IntArray.full vis1_pre n_pre vis1_m )
  **  (IntArray.full fin_pre n_pre fin_m )
  **  (IntArray.full timer_p_pre 1 (cons (timer_m) ((@nil Z))) )
.

Definition dfs1_partial_solve_wit_4 := dfs1_partial_solve_wit_4_pure -> dfs1_partial_solve_wit_4_aux.

Definition dfs1_partial_solve_wit_5 := 
forall (timer_p_pre: Z) (fin_pre: Z) (vis1_pre: Z) (radj_pre: Z) (n_pre: Z) (u_pre: Z) (radj_rows_low_level_spec: (@list (@list Z))) (X_low_level_spec: (unit -> (KSt -> Prop))) (g_low_level_spec: AdjGraph) (rem: (@list Z)) (cur: Z) (head: Z) (vis1_m: (@list Z)) (fin_m: (@list Z)) (timer_m: Z) (processed: (@list Z)) (PreH1 : (cur = 0)) (PreH2 : (safeExec (pre_dfs1 (g_low_level_spec) (vis1_m) (fin_m) (timer_m)) (dfs_finish_from (u_pre) ((edges_of (u_pre) (processed)))) X_low_level_spec )) (PreH3 : (0 <= u_pre)) (PreH4 : (u_pre < n_pre)) (PreH5 : (n_pre <= INT_MAX)) ,
  (SllPtrArray.missing_i radj_pre n_pre u_pre head radj_rows_low_level_spec )
  **  (sllseg head cur processed )
  **  (sll cur rem )
  **  (IntArray.full vis1_pre n_pre vis1_m )
  **  (IntArray.full fin_pre n_pre fin_m )
  **  (IntArray.full timer_p_pre 1 (cons (timer_m) ((@nil Z))) )
|--
  “ (cur = 0) ” 
  &&  “ (safeExec (pre_dfs1 (g_low_level_spec) (vis1_m) (fin_m) (timer_m)) (dfs_finish_from (u_pre) ((edges_of (u_pre) (processed)))) X_low_level_spec ) ” 
  &&  “ (0 <= u_pre) ” 
  &&  “ (u_pre < n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ”
  &&  (((timer_p_pre + (0 * sizeof(INT) ) )) # Int  |-> (Znth 0 (cons (timer_m) ((@nil Z))) 0))
  **  (IntArray.missing_i timer_p_pre 0 0 1 (cons (timer_m) ((@nil Z))) )
  **  (SllPtrArray.missing_i radj_pre n_pre u_pre head radj_rows_low_level_spec )
  **  (sllseg head cur processed )
  **  (sll cur rem )
  **  (IntArray.full vis1_pre n_pre vis1_m )
  **  (IntArray.full fin_pre n_pre fin_m )
.

Definition dfs1_partial_solve_wit_6 := 
forall (timer_p_pre: Z) (fin_pre: Z) (vis1_pre: Z) (radj_pre: Z) (n_pre: Z) (u_pre: Z) (radj_rows_low_level_spec: (@list (@list Z))) (X_low_level_spec: (unit -> (KSt -> Prop))) (g_low_level_spec: AdjGraph) (head: Z) (vis1_m: (@list Z)) (fin_m: (@list Z)) (timer_m: Z) (fin_m_set: (@list Z)) (timer_m_set: Z) (PreH1 : (0 <= u_pre)) (PreH2 : (u_pre < n_pre)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (fin_m_set = (replace_Znth (u_pre) (timer_m) (fin_m)))) (PreH5 : (timer_m_set = (timer_m + 1 ))) (PreH6 : (safeExec (pre_dfs1 (g_low_level_spec) (vis1_m) (fin_m_set) (timer_m_set)) (return (tt)) X_low_level_spec )) ,
  (SllPtrArray.missing_i radj_pre n_pre u_pre head radj_rows_low_level_spec )
  **  (sll head (Znth (u_pre) (radj_rows_low_level_spec) ((@nil Z))) )
  **  (IntArray.full vis1_pre n_pre vis1_m )
  **  (IntArray.full fin_pre n_pre fin_m_set )
  **  (IntArray.full timer_p_pre 1 (cons (timer_m) ((@nil Z))) )
|--
  “ (0 <= u_pre) ” 
  &&  “ (u_pre < n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (fin_m_set = (replace_Znth (u_pre) (timer_m) (fin_m))) ” 
  &&  “ (timer_m_set = (timer_m + 1 )) ” 
  &&  “ (safeExec (pre_dfs1 (g_low_level_spec) (vis1_m) (fin_m_set) (timer_m_set)) (return (tt)) X_low_level_spec ) ”
  &&  (((fin_pre + (u_pre * sizeof(INT) ) )) # Int  |->_)
  **  (IntArray.missing_i fin_pre u_pre 0 n_pre fin_m_set )
  **  (SllPtrArray.missing_i radj_pre n_pre u_pre head radj_rows_low_level_spec )
  **  (sll head (Znth (u_pre) (radj_rows_low_level_spec) ((@nil Z))) )
  **  (IntArray.full vis1_pre n_pre vis1_m )
  **  (IntArray.full timer_p_pre 1 (cons (timer_m) ((@nil Z))) )
.

Definition dfs1_partial_solve_wit_7 := 
forall (timer_p_pre: Z) (fin_pre: Z) (vis1_pre: Z) (radj_pre: Z) (n_pre: Z) (u_pre: Z) (radj_rows_low_level_spec: (@list (@list Z))) (X_low_level_spec: (unit -> (KSt -> Prop))) (g_low_level_spec: AdjGraph) (head: Z) (vis1_m: (@list Z)) (fin_m: (@list Z)) (timer_m: Z) (fin_m_set: (@list Z)) (timer_m_set: Z) (PreH1 : (0 <= u_pre)) (PreH2 : (u_pre < n_pre)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (fin_m_set = (replace_Znth (u_pre) (timer_m) (fin_m)))) (PreH5 : (timer_m_set = (timer_m + 1 ))) (PreH6 : (safeExec (pre_dfs1 (g_low_level_spec) (vis1_m) (fin_m_set) (timer_m_set)) (return (tt)) X_low_level_spec )) ,
  (IntArray.full fin_pre n_pre (replace_Znth (u_pre) (timer_m) (fin_m_set)) )
  **  (SllPtrArray.missing_i radj_pre n_pre u_pre head radj_rows_low_level_spec )
  **  (sll head (Znth (u_pre) (radj_rows_low_level_spec) ((@nil Z))) )
  **  (IntArray.full vis1_pre n_pre vis1_m )
  **  (IntArray.full timer_p_pre 1 (cons (timer_m) ((@nil Z))) )
|--
  “ (0 <= u_pre) ” 
  &&  “ (u_pre < n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (fin_m_set = (replace_Znth (u_pre) (timer_m) (fin_m))) ” 
  &&  “ (timer_m_set = (timer_m + 1 )) ” 
  &&  “ (safeExec (pre_dfs1 (g_low_level_spec) (vis1_m) (fin_m_set) (timer_m_set)) (return (tt)) X_low_level_spec ) ”
  &&  (((timer_p_pre + (0 * sizeof(INT) ) )) # Int  |->_)
  **  (IntArray.missing_i timer_p_pre 0 0 1 (cons (timer_m) ((@nil Z))) )
  **  (IntArray.full fin_pre n_pre (replace_Znth (u_pre) (timer_m) (fin_m_set)) )
  **  (SllPtrArray.missing_i radj_pre n_pre u_pre head radj_rows_low_level_spec )
  **  (sll head (Znth (u_pre) (radj_rows_low_level_spec) ((@nil Z))) )
  **  (IntArray.full vis1_pre n_pre vis1_m )
.

(*----- Function dfs2 -----*)

Definition dfs2_safety_wit_1 := 
forall (sid_pre: Z) (vis2_pre: Z) (fadj_pre: Z) (n_pre: Z) (u_pre: Z) (root_pre: Z) (fadj_rows_low_level_spec: (@list (@list Z))) (X_low_level_spec: (unit -> (KSt -> Prop))) (sid_l_low_level_spec: (@list Z)) (vis2_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (PreH1 : (safeExec (pre_dfs2 (g_low_level_spec) (vis2_l_low_level_spec) (sid_l_low_level_spec)) (dfs_scc (root_pre) (u_pre)) X_low_level_spec )) (PreH2 : (0 <= root_pre)) (PreH3 : (root_pre < n_pre)) (PreH4 : (0 <= u_pre)) (PreH5 : (u_pre < n_pre)) (PreH6 : (n_pre <= INT_MAX)) ,
  ((( &( "sid" ) )) # Ptr  |-> sid_pre)
  **  ((( &( "vis2" ) )) # Ptr  |-> vis2_pre)
  **  ((( &( "fadj" ) )) # Ptr  |-> fadj_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "u" ) )) # Int  |-> u_pre)
  **  ((( &( "root" ) )) # Int  |-> root_pre)
  **  (SllPtrArray.full fadj_pre n_pre fadj_rows_low_level_spec )
  **  (IntArray.full vis2_pre n_pre vis2_l_low_level_spec )
  **  (IntArray.full sid_pre n_pre sid_l_low_level_spec )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition dfs2_safety_wit_2 := 
forall (sid_pre: Z) (vis2_pre: Z) (fadj_pre: Z) (n_pre: Z) (u_pre: Z) (root_pre: Z) (fadj_rows_low_level_spec: (@list (@list Z))) (X_low_level_spec: (unit -> (KSt -> Prop))) (g_low_level_spec: AdjGraph) (rem: (@list Z)) (cur: Z) (head: Z) (vis2_m: (@list Z)) (sid_m: (@list Z)) (processed: (@list Z)) (PreH1 : (safeExec (pre_dfs2 (g_low_level_spec) (vis2_m) (sid_m)) (dfs_scc_from (root_pre) (u_pre) ((edges_of (u_pre) (processed)))) X_low_level_spec )) (PreH2 : (0 <= root_pre)) (PreH3 : (root_pre < n_pre)) (PreH4 : (0 <= u_pre)) (PreH5 : (u_pre < n_pre)) (PreH6 : (n_pre <= INT_MAX)) ,
  ((( &( "u" ) )) # Int  |-> u_pre)
  **  ((( &( "root" ) )) # Int  |-> root_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "fadj" ) )) # Ptr  |-> fadj_pre)
  **  ((( &( "vis2" ) )) # Ptr  |-> vis2_pre)
  **  ((( &( "sid" ) )) # Ptr  |-> sid_pre)
  **  (SllPtrArray.missing_i fadj_pre n_pre u_pre head fadj_rows_low_level_spec )
  **  ((( &( "cur" ) )) # Ptr  |-> cur)
  **  (sllseg head cur processed )
  **  (sll cur rem )
  **  (IntArray.full vis2_pre n_pre vis2_m )
  **  (IntArray.full sid_pre n_pre sid_m )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition dfs2_safety_wit_3 := 
forall (fadj_rows_low_level_spec: (@list (@list Z))) (X_low_level_spec: (unit -> (KSt -> Prop))) (g_low_level_spec: AdjGraph) (head: Z) (processed: (@list Z)) (rem: (@list Z)) (vis2_m: (@list Z)) (sid_m: (@list Z)) (vdata: Z) (rest: (@list Z)) (next_ptr: Z) (cur: Z) (n: Z) (u: Z) (root: Z) (fadj: Z) (vis2: Z) (sid: Z) (PreH1 : (cur <> 0)) (PreH2 : (0 <= vdata)) (PreH3 : (vdata < n)) (PreH4 : (n <= INT_MAX)) (PreH5 : (rem = (cons (vdata) (rest)))) (PreH6 : (safeExec (pre_dfs2 (g_low_level_spec) (vis2_m) (sid_m)) (dfs_scc_from (root) (u) ((edges_of (u) (processed)))) X_low_level_spec )) ,
  (IntArray.full vis2 n vis2_m )
  **  ((( &( "cur" ) )) # Ptr  |-> cur)
  **  ((( &( "v" ) )) # Int  |-> vdata)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "u" ) )) # Int  |-> u)
  **  ((( &( "root" ) )) # Int  |-> root)
  **  ((( &( "fadj" ) )) # Ptr  |-> fadj)
  **  (SllPtrArray.missing_i fadj n u head fadj_rows_low_level_spec )
  **  (sllseg head cur processed )
  **  ((&((cur)  # "list" ->ₛ "data")) # Int  |-> vdata)
  **  ((&((cur)  # "list" ->ₛ "next")) # Ptr  |-> next_ptr)
  **  (sll next_ptr rest )
  **  ((( &( "vis2" ) )) # Ptr  |-> vis2)
  **  ((( &( "sid" ) )) # Ptr  |-> sid)
  **  (IntArray.full sid n sid_m )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition dfs2_entail_wit_1 := 
(
forall (sid_pre: Z) (vis2_pre: Z) (fadj_pre: Z) (n_pre: Z) (u_pre: Z) (root_pre: Z) (fadj_rows_low_level_spec: (@list (@list Z))) (X_low_level_spec: (unit -> (KSt -> Prop))) (sid_l_low_level_spec: (@list Z)) (vis2_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (row_ptr: Z) (PreH1 : (safeExec (pre_dfs2 (g_low_level_spec) (vis2_l_low_level_spec) (sid_l_low_level_spec)) (dfs_scc (root_pre) (u_pre)) X_low_level_spec )) (PreH2 : (0 <= root_pre)) (PreH3 : (root_pre < n_pre)) (PreH4 : (0 <= u_pre)) (PreH5 : (u_pre < n_pre)) (PreH6 : (n_pre <= INT_MAX)) ,
  (SllPtrArray.full fadj_pre n_pre fadj_rows_low_level_spec )
  **  (IntArray.full sid_pre n_pre (replace_Znth (u_pre) ((Znth root_pre sid_l_low_level_spec 0)) (sid_l_low_level_spec)) )
  **  (IntArray.full vis2_pre n_pre (replace_Znth (u_pre) (1) (vis2_l_low_level_spec)) )
|--
  EX (rem: (@list Z))  (head: Z)  (vis2_m: (@list Z))  (sid_m: (@list Z))  (processed: (@list Z)) ,
  “ (safeExec (pre_dfs2 (g_low_level_spec) (vis2_m) (sid_m)) (dfs_scc_from (root_pre) (u_pre) ((edges_of (u_pre) (processed)))) X_low_level_spec ) ” 
  &&  “ (0 <= root_pre) ” 
  &&  “ (root_pre < n_pre) ” 
  &&  “ (0 <= u_pre) ” 
  &&  “ (u_pre < n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ”
  &&  (SllPtrArray.missing_i fadj_pre n_pre u_pre head fadj_rows_low_level_spec )
  **  (sllseg head row_ptr processed )
  **  (sll row_ptr rem )
  **  (IntArray.full vis2_pre n_pre vis2_m )
  **  (IntArray.full sid_pre n_pre sid_m )
) \/
(
forall (fadj_pre: Z) (n_pre: Z) (u_pre: Z) (root_pre: Z) (fadj_rows_low_level_spec: (@list (@list Z))) (X_low_level_spec: (unit -> (KSt -> Prop))) (sid_l_low_level_spec: (@list Z)) (vis2_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (row_ptr: Z) (PreH1 : (safeExec (pre_dfs2 (g_low_level_spec) (vis2_l_low_level_spec) (sid_l_low_level_spec)) (dfs_scc (root_pre) (u_pre)) X_low_level_spec )) (PreH2 : (0 <= root_pre)) (PreH3 : (root_pre < n_pre)) (PreH4 : (0 <= u_pre)) (PreH5 : (u_pre < n_pre)) (PreH6 : (n_pre <= INT_MAX)) ,
  (SllPtrArray.full fadj_pre n_pre fadj_rows_low_level_spec )
|--
  EX (rem: (@list Z))  (head: Z)  (processed: (@list Z)) ,
  “ (safeExec (pre_dfs2 (g_low_level_spec) ((replace_Znth (u_pre) (1) (vis2_l_low_level_spec))) ((replace_Znth (u_pre) ((Znth root_pre sid_l_low_level_spec 0)) (sid_l_low_level_spec)))) (dfs_scc_from (root_pre) (u_pre) ((edges_of (u_pre) (processed)))) X_low_level_spec ) ” 
  &&  “ (0 <= root_pre) ” 
  &&  “ (root_pre < n_pre) ” 
  &&  “ (0 <= u_pre) ” 
  &&  “ (u_pre < n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ”
  &&  (SllPtrArray.missing_i fadj_pre n_pre u_pre head fadj_rows_low_level_spec )
  **  (sllseg head row_ptr processed )
  **  (sll row_ptr rem )
).

Definition dfs2_entail_wit_2 := 
(
forall (sid_pre: Z) (vis2_pre: Z) (fadj_pre: Z) (n_pre: Z) (u_pre: Z) (root_pre: Z) (fadj_rows_low_level_spec: (@list (@list Z))) (X_low_level_spec: (unit -> (KSt -> Prop))) (g_low_level_spec: AdjGraph) (cur: Z) (head: Z) (processed: (@list Z)) (rem: (@list Z)) (vis2_m: (@list Z)) (sid_m: (@list Z)) (PreH1 : (cur <> 0)) (PreH2 : (safeExec (pre_dfs2 (g_low_level_spec) (vis2_m) (sid_m)) (dfs_scc_from (root_pre) (u_pre) ((edges_of (u_pre) (processed)))) X_low_level_spec )) (PreH3 : (0 <= root_pre)) (PreH4 : (root_pre < n_pre)) (PreH5 : (0 <= u_pre)) (PreH6 : (u_pre < n_pre)) (PreH7 : (n_pre <= INT_MAX)) ,
  ((( &( "v" ) )) # Int  |->_)
  **  (SllPtrArray.missing_i fadj_pre n_pre u_pre head fadj_rows_low_level_spec )
  **  (sllseg head cur processed )
  **  (sll cur rem )
  **  (IntArray.full vis2_pre n_pre vis2_m )
  **  (IntArray.full sid_pre n_pre sid_m )
|--
  EX (next_ptr: Z)  (rest: (@list Z))  (vdata: Z) ,
  “ (cur <> 0) ” 
  &&  “ (0 <= vdata) ” 
  &&  “ (vdata < n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (rem = (cons (vdata) (rest))) ” 
  &&  “ (safeExec (pre_dfs2 (g_low_level_spec) (vis2_m) (sid_m)) (dfs_scc_from (root_pre) (u_pre) ((edges_of (u_pre) (processed)))) X_low_level_spec ) ”
  &&  ((( &( "v" ) )) # Int  |-> vdata)
  **  (SllPtrArray.missing_i fadj_pre n_pre u_pre head fadj_rows_low_level_spec )
  **  (sllseg head cur processed )
  **  ((&((cur)  # "list" ->ₛ "data")) # Int  |-> vdata)
  **  ((&((cur)  # "list" ->ₛ "next")) # Ptr  |-> next_ptr)
  **  (sll next_ptr rest )
  **  (IntArray.full vis2_pre n_pre vis2_m )
  **  (IntArray.full sid_pre n_pre sid_m )
) \/
(
forall (n_pre: Z) (u_pre: Z) (root_pre: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (g_low_level_spec: AdjGraph) (cur: Z) (head: Z) (processed: (@list Z)) (rem: (@list Z)) (vis2_m: (@list Z)) (sid_m: (@list Z)) (x: Z) (l0: (@list Z)) (PreH1 : (rem = (cons (x) (l0)))) (PreH2 : (cur <> 0)) (PreH3 : (safeExec (pre_dfs2 (g_low_level_spec) (vis2_m) (sid_m)) (dfs_scc_from (root_pre) (u_pre) ((edges_of (u_pre) (processed)))) X_low_level_spec )) (PreH4 : (0 <= root_pre)) (PreH5 : (root_pre < n_pre)) (PreH6 : (0 <= u_pre)) (PreH7 : (u_pre < n_pre)) (PreH8 : (n_pre <= INT_MAX)) ,
  ((( &( "v" ) )) # Int  |->_)
  **  (sllseg head cur processed )
|--
  “ (x < n_pre) ” 
  &&  “ (0 <= x) ”
  &&  ((( &( "v" ) )) # Int  |-> x)
  **  (sllseg head cur processed )
).

Definition dfs2_entail_wit_2_split_goal_1 := 
forall (n_pre: Z) (u_pre: Z) (root_pre: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (g_low_level_spec: AdjGraph) (cur: Z) (head: Z) (processed: (@list Z)) (rem: (@list Z)) (vis2_m: (@list Z)) (sid_m: (@list Z)) (x: Z) (l0: (@list Z)) (PreH1 : (rem = (cons (x) (l0)))) (PreH2 : (cur <> 0)) (PreH3 : (safeExec (pre_dfs2 (g_low_level_spec) (vis2_m) (sid_m)) (dfs_scc_from (root_pre) (u_pre) ((edges_of (u_pre) (processed)))) X_low_level_spec )) (PreH4 : (0 <= root_pre)) (PreH5 : (root_pre < n_pre)) (PreH6 : (0 <= u_pre)) (PreH7 : (u_pre < n_pre)) (PreH8 : (n_pre <= INT_MAX)) ,
  ((( &( "v" ) )) # Int  |->_)
  **  (sllseg head cur processed )
|--
  “ (x < n_pre) ”
.

Definition dfs2_entail_wit_2_split_goal_2 := 
forall (n_pre: Z) (u_pre: Z) (root_pre: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (g_low_level_spec: AdjGraph) (cur: Z) (head: Z) (processed: (@list Z)) (rem: (@list Z)) (vis2_m: (@list Z)) (sid_m: (@list Z)) (x: Z) (l0: (@list Z)) (PreH1 : (rem = (cons (x) (l0)))) (PreH2 : (cur <> 0)) (PreH3 : (safeExec (pre_dfs2 (g_low_level_spec) (vis2_m) (sid_m)) (dfs_scc_from (root_pre) (u_pre) ((edges_of (u_pre) (processed)))) X_low_level_spec )) (PreH4 : (0 <= root_pre)) (PreH5 : (root_pre < n_pre)) (PreH6 : (0 <= u_pre)) (PreH7 : (u_pre < n_pre)) (PreH8 : (n_pre <= INT_MAX)) ,
  ((( &( "v" ) )) # Int  |->_)
  **  (sllseg head cur processed )
|--
  “ (0 <= x) ”
.

Definition dfs2_entail_wit_2_split_goal_spatial := 
forall (n_pre: Z) (u_pre: Z) (root_pre: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (g_low_level_spec: AdjGraph) (cur: Z) (head: Z) (processed: (@list Z)) (rem: (@list Z)) (vis2_m: (@list Z)) (sid_m: (@list Z)) (x: Z) (l0: (@list Z)) (PreH1 : (rem = (cons (x) (l0)))) (PreH2 : (cur <> 0)) (PreH3 : (safeExec (pre_dfs2 (g_low_level_spec) (vis2_m) (sid_m)) (dfs_scc_from (root_pre) (u_pre) ((edges_of (u_pre) (processed)))) X_low_level_spec )) (PreH4 : (0 <= root_pre)) (PreH5 : (root_pre < n_pre)) (PreH6 : (0 <= u_pre)) (PreH7 : (u_pre < n_pre)) (PreH8 : (n_pre <= INT_MAX)) ,
  ((( &( "v" ) )) # Int  |->_)
  **  (sllseg head cur processed )
|--
  ((( &( "v" ) )) # Int  |-> x)
  **  (sllseg head cur processed )
.

Definition dfs2_entail_wit_3 := 
(
forall (sid_pre: Z) (vis2_pre: Z) (fadj_pre: Z) (n_pre: Z) (u_pre: Z) (root_pre: Z) (fadj_rows_low_level_spec: (@list (@list Z))) (X_low_level_spec: (unit -> (KSt -> Prop))) (g_low_level_spec: AdjGraph) (head: Z) (processed: (@list Z)) (rem: (@list Z)) (vis2_m: (@list Z)) (sid_m: (@list Z)) (vdata: Z) (rest: (@list Z)) (next_ptr: Z) (cur: Z) (n: Z) (u: Z) (root: Z) (fadj: Z) (vis2: Z) (sid: Z) (PreH1 : ((Znth vdata vis2_m 0) = 0)) (PreH2 : (cur <> 0)) (PreH3 : (0 <= vdata)) (PreH4 : (vdata < n)) (PreH5 : (n <= INT_MAX)) (PreH6 : (rem = (cons (vdata) (rest)))) (PreH7 : (safeExec (pre_dfs2 (g_low_level_spec) (vis2_m) (sid_m)) (dfs_scc_from (root) (u) ((edges_of (u) (processed)))) X_low_level_spec )) ,
  (IntArray.full vis2 n vis2_m )
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "u" ) )) # Int  |-> u)
  **  ((( &( "root" ) )) # Int  |-> root)
  **  ((( &( "fadj" ) )) # Ptr  |-> fadj)
  **  (SllPtrArray.missing_i fadj n u head fadj_rows_low_level_spec )
  **  (sllseg head cur processed )
  **  ((&((cur)  # "list" ->ₛ "data")) # Int  |-> vdata)
  **  ((&((cur)  # "list" ->ₛ "next")) # Ptr  |-> next_ptr)
  **  (sll next_ptr rest )
  **  ((( &( "vis2" ) )) # Ptr  |-> vis2)
  **  ((( &( "sid" ) )) # Ptr  |-> sid)
  **  (IntArray.full sid n sid_m )
|--
  “ (cur <> 0) ” 
  &&  “ (0 <= root_pre) ” 
  &&  “ (root_pre < n_pre) ” 
  &&  “ (0 <= u_pre) ” 
  &&  “ (u_pre < n_pre) ” 
  &&  “ (0 <= vdata) ” 
  &&  “ (vdata < n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ ((Znth (vdata) (vis2_m) (0)) = 0) ” 
  &&  “ (safeExec (pre_dfs2 (g_low_level_spec) (vis2_m) (sid_m)) (dfs_scc (root_pre) (vdata)) X_low_level_spec ) ”
  &&  ((( &( "root" ) )) # Int  |-> root_pre)
  **  ((( &( "u" ) )) # Int  |-> u_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "fadj" ) )) # Ptr  |-> fadj_pre)
  **  ((( &( "vis2" ) )) # Ptr  |-> vis2_pre)
  **  ((( &( "sid" ) )) # Ptr  |-> sid_pre)
  **  (SllPtrArray.full fadj_pre n_pre fadj_rows_low_level_spec )
  **  (IntArray.full vis2_pre n_pre vis2_m )
  **  (IntArray.full sid_pre n_pre sid_m )
) \/
(
forall (sid_pre: Z) (vis2_pre: Z) (fadj_pre: Z) (n_pre: Z) (u_pre: Z) (root_pre: Z) (fadj_rows_low_level_spec: (@list (@list Z))) (X_low_level_spec: (unit -> (KSt -> Prop))) (g_low_level_spec: AdjGraph) (head: Z) (processed: (@list Z)) (rem: (@list Z)) (vis2_m: (@list Z)) (sid_m: (@list Z)) (vdata: Z) (rest: (@list Z)) (next_ptr: Z) (cur: Z) (n: Z) (u: Z) (root: Z) (fadj: Z) (vis2: Z) (sid: Z) (PreH1 : (vdata <= INT_MAX)) (PreH2 : (vdata >= INT_MIN)) (PreH3 : ((Znth vdata vis2_m 0) = 0)) (PreH4 : (cur <> 0)) (PreH5 : (0 <= vdata)) (PreH6 : (vdata < n)) (PreH7 : (n <= INT_MAX)) (PreH8 : (rem = (cons (vdata) (rest)))) (PreH9 : (safeExec (pre_dfs2 (g_low_level_spec) (vis2_m) (sid_m)) (dfs_scc_from (root) (u) ((edges_of (u) (processed)))) X_low_level_spec )) ,
  (IntArray.full vis2 n vis2_m )
  **  (SllPtrArray.missing_i fadj n u head fadj_rows_low_level_spec )
  **  (sllseg head cur processed )
  **  ((&((cur)  # "list" ->ₛ "data")) # Int  |-> vdata)
  **  ((&((cur)  # "list" ->ₛ "next")) # Ptr  |-> next_ptr)
  **  (sll next_ptr rest )
  **  (IntArray.full sid n sid_m )
|--
  “ (safeExec (pre_dfs2 (g_low_level_spec) (vis2_m) (sid_m)) (dfs_scc (root_pre) (vdata)) X_low_level_spec ) ” 
  &&  “ ((Znth (vdata) (vis2_m) (0)) = 0) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (vdata < n_pre) ” 
  &&  “ (u_pre < n_pre) ” 
  &&  “ (0 <= u_pre) ” 
  &&  “ (root_pre < n_pre) ” 
  &&  “ (0 <= root_pre) ” 
  &&  “ (n = n_pre) ” 
  &&  “ (u = u_pre) ” 
  &&  “ (root = root_pre) ” 
  &&  “ (fadj = fadj_pre) ” 
  &&  “ (vis2 = vis2_pre) ” 
  &&  “ (sid = sid_pre) ”
  &&  (SllPtrArray.full fadj_pre n_pre fadj_rows_low_level_spec )
  **  (IntArray.full vis2_pre n_pre vis2_m )
  **  (IntArray.full sid_pre n_pre sid_m )
).

Definition dfs2_entail_wit_3_split_goal_1 := 
forall (root_pre: Z) (fadj_rows_low_level_spec: (@list (@list Z))) (X_low_level_spec: (unit -> (KSt -> Prop))) (g_low_level_spec: AdjGraph) (head: Z) (processed: (@list Z)) (rem: (@list Z)) (vis2_m: (@list Z)) (sid_m: (@list Z)) (vdata: Z) (rest: (@list Z)) (next_ptr: Z) (cur: Z) (n: Z) (u: Z) (root: Z) (fadj: Z) (vis2: Z) (sid: Z) (PreH1 : (vdata <= INT_MAX)) (PreH2 : (vdata >= INT_MIN)) (PreH3 : ((Znth vdata vis2_m 0) = 0)) (PreH4 : (cur <> 0)) (PreH5 : (0 <= vdata)) (PreH6 : (vdata < n)) (PreH7 : (n <= INT_MAX)) (PreH8 : (rem = (cons (vdata) (rest)))) (PreH9 : (safeExec (pre_dfs2 (g_low_level_spec) (vis2_m) (sid_m)) (dfs_scc_from (root) (u) ((edges_of (u) (processed)))) X_low_level_spec )) ,
  (IntArray.full vis2 n vis2_m )
  **  (SllPtrArray.missing_i fadj n u head fadj_rows_low_level_spec )
  **  (sllseg head cur processed )
  **  ((&((cur)  # "list" ->ₛ "data")) # Int  |-> vdata)
  **  ((&((cur)  # "list" ->ₛ "next")) # Ptr  |-> next_ptr)
  **  (sll next_ptr rest )
  **  (IntArray.full sid n sid_m )
|--
  “ (safeExec (pre_dfs2 (g_low_level_spec) (vis2_m) (sid_m)) (dfs_scc (root_pre) (vdata)) X_low_level_spec ) ”
.

Definition dfs2_entail_wit_3_split_goal_2 := 
forall (fadj_rows_low_level_spec: (@list (@list Z))) (X_low_level_spec: (unit -> (KSt -> Prop))) (g_low_level_spec: AdjGraph) (head: Z) (processed: (@list Z)) (rem: (@list Z)) (vis2_m: (@list Z)) (sid_m: (@list Z)) (vdata: Z) (rest: (@list Z)) (next_ptr: Z) (cur: Z) (n: Z) (u: Z) (root: Z) (fadj: Z) (vis2: Z) (sid: Z) (PreH1 : (vdata <= INT_MAX)) (PreH2 : (vdata >= INT_MIN)) (PreH3 : ((Znth vdata vis2_m 0) = 0)) (PreH4 : (cur <> 0)) (PreH5 : (0 <= vdata)) (PreH6 : (vdata < n)) (PreH7 : (n <= INT_MAX)) (PreH8 : (rem = (cons (vdata) (rest)))) (PreH9 : (safeExec (pre_dfs2 (g_low_level_spec) (vis2_m) (sid_m)) (dfs_scc_from (root) (u) ((edges_of (u) (processed)))) X_low_level_spec )) ,
  (IntArray.full vis2 n vis2_m )
  **  (SllPtrArray.missing_i fadj n u head fadj_rows_low_level_spec )
  **  (sllseg head cur processed )
  **  ((&((cur)  # "list" ->ₛ "data")) # Int  |-> vdata)
  **  ((&((cur)  # "list" ->ₛ "next")) # Ptr  |-> next_ptr)
  **  (sll next_ptr rest )
  **  (IntArray.full sid n sid_m )
|--
  “ ((Znth (vdata) (vis2_m) (0)) = 0) ”
.

Definition dfs2_entail_wit_3_split_goal_3 := 
forall (n_pre: Z) (fadj_rows_low_level_spec: (@list (@list Z))) (X_low_level_spec: (unit -> (KSt -> Prop))) (g_low_level_spec: AdjGraph) (head: Z) (processed: (@list Z)) (rem: (@list Z)) (vis2_m: (@list Z)) (sid_m: (@list Z)) (vdata: Z) (rest: (@list Z)) (next_ptr: Z) (cur: Z) (n: Z) (u: Z) (root: Z) (fadj: Z) (vis2: Z) (sid: Z) (PreH1 : (vdata <= INT_MAX)) (PreH2 : (vdata >= INT_MIN)) (PreH3 : ((Znth vdata vis2_m 0) = 0)) (PreH4 : (cur <> 0)) (PreH5 : (0 <= vdata)) (PreH6 : (vdata < n)) (PreH7 : (n <= INT_MAX)) (PreH8 : (rem = (cons (vdata) (rest)))) (PreH9 : (safeExec (pre_dfs2 (g_low_level_spec) (vis2_m) (sid_m)) (dfs_scc_from (root) (u) ((edges_of (u) (processed)))) X_low_level_spec )) ,
  (IntArray.full vis2 n vis2_m )
  **  (SllPtrArray.missing_i fadj n u head fadj_rows_low_level_spec )
  **  (sllseg head cur processed )
  **  ((&((cur)  # "list" ->ₛ "data")) # Int  |-> vdata)
  **  ((&((cur)  # "list" ->ₛ "next")) # Ptr  |-> next_ptr)
  **  (sll next_ptr rest )
  **  (IntArray.full sid n sid_m )
|--
  “ (n_pre <= INT_MAX) ”
.

Definition dfs2_entail_wit_3_split_goal_4 := 
forall (n_pre: Z) (fadj_rows_low_level_spec: (@list (@list Z))) (X_low_level_spec: (unit -> (KSt -> Prop))) (g_low_level_spec: AdjGraph) (head: Z) (processed: (@list Z)) (rem: (@list Z)) (vis2_m: (@list Z)) (sid_m: (@list Z)) (vdata: Z) (rest: (@list Z)) (next_ptr: Z) (cur: Z) (n: Z) (u: Z) (root: Z) (fadj: Z) (vis2: Z) (sid: Z) (PreH1 : (vdata <= INT_MAX)) (PreH2 : (vdata >= INT_MIN)) (PreH3 : ((Znth vdata vis2_m 0) = 0)) (PreH4 : (cur <> 0)) (PreH5 : (0 <= vdata)) (PreH6 : (vdata < n)) (PreH7 : (n <= INT_MAX)) (PreH8 : (rem = (cons (vdata) (rest)))) (PreH9 : (safeExec (pre_dfs2 (g_low_level_spec) (vis2_m) (sid_m)) (dfs_scc_from (root) (u) ((edges_of (u) (processed)))) X_low_level_spec )) ,
  (IntArray.full vis2 n vis2_m )
  **  (SllPtrArray.missing_i fadj n u head fadj_rows_low_level_spec )
  **  (sllseg head cur processed )
  **  ((&((cur)  # "list" ->ₛ "data")) # Int  |-> vdata)
  **  ((&((cur)  # "list" ->ₛ "next")) # Ptr  |-> next_ptr)
  **  (sll next_ptr rest )
  **  (IntArray.full sid n sid_m )
|--
  “ (vdata < n_pre) ”
.

Definition dfs2_entail_wit_3_split_goal_5 := 
forall (n_pre: Z) (u_pre: Z) (fadj_rows_low_level_spec: (@list (@list Z))) (X_low_level_spec: (unit -> (KSt -> Prop))) (g_low_level_spec: AdjGraph) (head: Z) (processed: (@list Z)) (rem: (@list Z)) (vis2_m: (@list Z)) (sid_m: (@list Z)) (vdata: Z) (rest: (@list Z)) (next_ptr: Z) (cur: Z) (n: Z) (u: Z) (root: Z) (fadj: Z) (vis2: Z) (sid: Z) (PreH1 : (vdata <= INT_MAX)) (PreH2 : (vdata >= INT_MIN)) (PreH3 : ((Znth vdata vis2_m 0) = 0)) (PreH4 : (cur <> 0)) (PreH5 : (0 <= vdata)) (PreH6 : (vdata < n)) (PreH7 : (n <= INT_MAX)) (PreH8 : (rem = (cons (vdata) (rest)))) (PreH9 : (safeExec (pre_dfs2 (g_low_level_spec) (vis2_m) (sid_m)) (dfs_scc_from (root) (u) ((edges_of (u) (processed)))) X_low_level_spec )) ,
  (IntArray.full vis2 n vis2_m )
  **  (SllPtrArray.missing_i fadj n u head fadj_rows_low_level_spec )
  **  (sllseg head cur processed )
  **  ((&((cur)  # "list" ->ₛ "data")) # Int  |-> vdata)
  **  ((&((cur)  # "list" ->ₛ "next")) # Ptr  |-> next_ptr)
  **  (sll next_ptr rest )
  **  (IntArray.full sid n sid_m )
|--
  “ (u_pre < n_pre) ”
.

Definition dfs2_entail_wit_3_split_goal_6 := 
forall (u_pre: Z) (fadj_rows_low_level_spec: (@list (@list Z))) (X_low_level_spec: (unit -> (KSt -> Prop))) (g_low_level_spec: AdjGraph) (head: Z) (processed: (@list Z)) (rem: (@list Z)) (vis2_m: (@list Z)) (sid_m: (@list Z)) (vdata: Z) (rest: (@list Z)) (next_ptr: Z) (cur: Z) (n: Z) (u: Z) (root: Z) (fadj: Z) (vis2: Z) (sid: Z) (PreH1 : (vdata <= INT_MAX)) (PreH2 : (vdata >= INT_MIN)) (PreH3 : ((Znth vdata vis2_m 0) = 0)) (PreH4 : (cur <> 0)) (PreH5 : (0 <= vdata)) (PreH6 : (vdata < n)) (PreH7 : (n <= INT_MAX)) (PreH8 : (rem = (cons (vdata) (rest)))) (PreH9 : (safeExec (pre_dfs2 (g_low_level_spec) (vis2_m) (sid_m)) (dfs_scc_from (root) (u) ((edges_of (u) (processed)))) X_low_level_spec )) ,
  (IntArray.full vis2 n vis2_m )
  **  (SllPtrArray.missing_i fadj n u head fadj_rows_low_level_spec )
  **  (sllseg head cur processed )
  **  ((&((cur)  # "list" ->ₛ "data")) # Int  |-> vdata)
  **  ((&((cur)  # "list" ->ₛ "next")) # Ptr  |-> next_ptr)
  **  (sll next_ptr rest )
  **  (IntArray.full sid n sid_m )
|--
  “ (0 <= u_pre) ”
.

Definition dfs2_entail_wit_3_split_goal_7 := 
forall (n_pre: Z) (root_pre: Z) (fadj_rows_low_level_spec: (@list (@list Z))) (X_low_level_spec: (unit -> (KSt -> Prop))) (g_low_level_spec: AdjGraph) (head: Z) (processed: (@list Z)) (rem: (@list Z)) (vis2_m: (@list Z)) (sid_m: (@list Z)) (vdata: Z) (rest: (@list Z)) (next_ptr: Z) (cur: Z) (n: Z) (u: Z) (root: Z) (fadj: Z) (vis2: Z) (sid: Z) (PreH1 : (vdata <= INT_MAX)) (PreH2 : (vdata >= INT_MIN)) (PreH3 : ((Znth vdata vis2_m 0) = 0)) (PreH4 : (cur <> 0)) (PreH5 : (0 <= vdata)) (PreH6 : (vdata < n)) (PreH7 : (n <= INT_MAX)) (PreH8 : (rem = (cons (vdata) (rest)))) (PreH9 : (safeExec (pre_dfs2 (g_low_level_spec) (vis2_m) (sid_m)) (dfs_scc_from (root) (u) ((edges_of (u) (processed)))) X_low_level_spec )) ,
  (IntArray.full vis2 n vis2_m )
  **  (SllPtrArray.missing_i fadj n u head fadj_rows_low_level_spec )
  **  (sllseg head cur processed )
  **  ((&((cur)  # "list" ->ₛ "data")) # Int  |-> vdata)
  **  ((&((cur)  # "list" ->ₛ "next")) # Ptr  |-> next_ptr)
  **  (sll next_ptr rest )
  **  (IntArray.full sid n sid_m )
|--
  “ (root_pre < n_pre) ”
.

Definition dfs2_entail_wit_3_split_goal_8 := 
forall (root_pre: Z) (fadj_rows_low_level_spec: (@list (@list Z))) (X_low_level_spec: (unit -> (KSt -> Prop))) (g_low_level_spec: AdjGraph) (head: Z) (processed: (@list Z)) (rem: (@list Z)) (vis2_m: (@list Z)) (sid_m: (@list Z)) (vdata: Z) (rest: (@list Z)) (next_ptr: Z) (cur: Z) (n: Z) (u: Z) (root: Z) (fadj: Z) (vis2: Z) (sid: Z) (PreH1 : (vdata <= INT_MAX)) (PreH2 : (vdata >= INT_MIN)) (PreH3 : ((Znth vdata vis2_m 0) = 0)) (PreH4 : (cur <> 0)) (PreH5 : (0 <= vdata)) (PreH6 : (vdata < n)) (PreH7 : (n <= INT_MAX)) (PreH8 : (rem = (cons (vdata) (rest)))) (PreH9 : (safeExec (pre_dfs2 (g_low_level_spec) (vis2_m) (sid_m)) (dfs_scc_from (root) (u) ((edges_of (u) (processed)))) X_low_level_spec )) ,
  (IntArray.full vis2 n vis2_m )
  **  (SllPtrArray.missing_i fadj n u head fadj_rows_low_level_spec )
  **  (sllseg head cur processed )
  **  ((&((cur)  # "list" ->ₛ "data")) # Int  |-> vdata)
  **  ((&((cur)  # "list" ->ₛ "next")) # Ptr  |-> next_ptr)
  **  (sll next_ptr rest )
  **  (IntArray.full sid n sid_m )
|--
  “ (0 <= root_pre) ”
.

Definition dfs2_entail_wit_3_split_goal_9 := 
forall (n_pre: Z) (fadj_rows_low_level_spec: (@list (@list Z))) (X_low_level_spec: (unit -> (KSt -> Prop))) (g_low_level_spec: AdjGraph) (head: Z) (processed: (@list Z)) (rem: (@list Z)) (vis2_m: (@list Z)) (sid_m: (@list Z)) (vdata: Z) (rest: (@list Z)) (next_ptr: Z) (cur: Z) (n: Z) (u: Z) (root: Z) (fadj: Z) (vis2: Z) (sid: Z) (PreH1 : (vdata <= INT_MAX)) (PreH2 : (vdata >= INT_MIN)) (PreH3 : ((Znth vdata vis2_m 0) = 0)) (PreH4 : (cur <> 0)) (PreH5 : (0 <= vdata)) (PreH6 : (vdata < n)) (PreH7 : (n <= INT_MAX)) (PreH8 : (rem = (cons (vdata) (rest)))) (PreH9 : (safeExec (pre_dfs2 (g_low_level_spec) (vis2_m) (sid_m)) (dfs_scc_from (root) (u) ((edges_of (u) (processed)))) X_low_level_spec )) ,
  (IntArray.full vis2 n vis2_m )
  **  (SllPtrArray.missing_i fadj n u head fadj_rows_low_level_spec )
  **  (sllseg head cur processed )
  **  ((&((cur)  # "list" ->ₛ "data")) # Int  |-> vdata)
  **  ((&((cur)  # "list" ->ₛ "next")) # Ptr  |-> next_ptr)
  **  (sll next_ptr rest )
  **  (IntArray.full sid n sid_m )
|--
  “ (n = n_pre) ”
.

Definition dfs2_entail_wit_3_split_goal_10 := 
forall (u_pre: Z) (fadj_rows_low_level_spec: (@list (@list Z))) (X_low_level_spec: (unit -> (KSt -> Prop))) (g_low_level_spec: AdjGraph) (head: Z) (processed: (@list Z)) (rem: (@list Z)) (vis2_m: (@list Z)) (sid_m: (@list Z)) (vdata: Z) (rest: (@list Z)) (next_ptr: Z) (cur: Z) (n: Z) (u: Z) (root: Z) (fadj: Z) (vis2: Z) (sid: Z) (PreH1 : (vdata <= INT_MAX)) (PreH2 : (vdata >= INT_MIN)) (PreH3 : ((Znth vdata vis2_m 0) = 0)) (PreH4 : (cur <> 0)) (PreH5 : (0 <= vdata)) (PreH6 : (vdata < n)) (PreH7 : (n <= INT_MAX)) (PreH8 : (rem = (cons (vdata) (rest)))) (PreH9 : (safeExec (pre_dfs2 (g_low_level_spec) (vis2_m) (sid_m)) (dfs_scc_from (root) (u) ((edges_of (u) (processed)))) X_low_level_spec )) ,
  (IntArray.full vis2 n vis2_m )
  **  (SllPtrArray.missing_i fadj n u head fadj_rows_low_level_spec )
  **  (sllseg head cur processed )
  **  ((&((cur)  # "list" ->ₛ "data")) # Int  |-> vdata)
  **  ((&((cur)  # "list" ->ₛ "next")) # Ptr  |-> next_ptr)
  **  (sll next_ptr rest )
  **  (IntArray.full sid n sid_m )
|--
  “ (u = u_pre) ”
.

Definition dfs2_entail_wit_3_split_goal_11 := 
forall (root_pre: Z) (fadj_rows_low_level_spec: (@list (@list Z))) (X_low_level_spec: (unit -> (KSt -> Prop))) (g_low_level_spec: AdjGraph) (head: Z) (processed: (@list Z)) (rem: (@list Z)) (vis2_m: (@list Z)) (sid_m: (@list Z)) (vdata: Z) (rest: (@list Z)) (next_ptr: Z) (cur: Z) (n: Z) (u: Z) (root: Z) (fadj: Z) (vis2: Z) (sid: Z) (PreH1 : (vdata <= INT_MAX)) (PreH2 : (vdata >= INT_MIN)) (PreH3 : ((Znth vdata vis2_m 0) = 0)) (PreH4 : (cur <> 0)) (PreH5 : (0 <= vdata)) (PreH6 : (vdata < n)) (PreH7 : (n <= INT_MAX)) (PreH8 : (rem = (cons (vdata) (rest)))) (PreH9 : (safeExec (pre_dfs2 (g_low_level_spec) (vis2_m) (sid_m)) (dfs_scc_from (root) (u) ((edges_of (u) (processed)))) X_low_level_spec )) ,
  (IntArray.full vis2 n vis2_m )
  **  (SllPtrArray.missing_i fadj n u head fadj_rows_low_level_spec )
  **  (sllseg head cur processed )
  **  ((&((cur)  # "list" ->ₛ "data")) # Int  |-> vdata)
  **  ((&((cur)  # "list" ->ₛ "next")) # Ptr  |-> next_ptr)
  **  (sll next_ptr rest )
  **  (IntArray.full sid n sid_m )
|--
  “ (root = root_pre) ”
.

Definition dfs2_entail_wit_3_split_goal_12 := 
forall (fadj_pre: Z) (fadj_rows_low_level_spec: (@list (@list Z))) (X_low_level_spec: (unit -> (KSt -> Prop))) (g_low_level_spec: AdjGraph) (head: Z) (processed: (@list Z)) (rem: (@list Z)) (vis2_m: (@list Z)) (sid_m: (@list Z)) (vdata: Z) (rest: (@list Z)) (next_ptr: Z) (cur: Z) (n: Z) (u: Z) (root: Z) (fadj: Z) (vis2: Z) (sid: Z) (PreH1 : (vdata <= INT_MAX)) (PreH2 : (vdata >= INT_MIN)) (PreH3 : ((Znth vdata vis2_m 0) = 0)) (PreH4 : (cur <> 0)) (PreH5 : (0 <= vdata)) (PreH6 : (vdata < n)) (PreH7 : (n <= INT_MAX)) (PreH8 : (rem = (cons (vdata) (rest)))) (PreH9 : (safeExec (pre_dfs2 (g_low_level_spec) (vis2_m) (sid_m)) (dfs_scc_from (root) (u) ((edges_of (u) (processed)))) X_low_level_spec )) ,
  (IntArray.full vis2 n vis2_m )
  **  (SllPtrArray.missing_i fadj n u head fadj_rows_low_level_spec )
  **  (sllseg head cur processed )
  **  ((&((cur)  # "list" ->ₛ "data")) # Int  |-> vdata)
  **  ((&((cur)  # "list" ->ₛ "next")) # Ptr  |-> next_ptr)
  **  (sll next_ptr rest )
  **  (IntArray.full sid n sid_m )
|--
  “ (fadj = fadj_pre) ”
.

Definition dfs2_entail_wit_3_split_goal_13 := 
forall (vis2_pre: Z) (fadj_rows_low_level_spec: (@list (@list Z))) (X_low_level_spec: (unit -> (KSt -> Prop))) (g_low_level_spec: AdjGraph) (head: Z) (processed: (@list Z)) (rem: (@list Z)) (vis2_m: (@list Z)) (sid_m: (@list Z)) (vdata: Z) (rest: (@list Z)) (next_ptr: Z) (cur: Z) (n: Z) (u: Z) (root: Z) (fadj: Z) (vis2: Z) (sid: Z) (PreH1 : (vdata <= INT_MAX)) (PreH2 : (vdata >= INT_MIN)) (PreH3 : ((Znth vdata vis2_m 0) = 0)) (PreH4 : (cur <> 0)) (PreH5 : (0 <= vdata)) (PreH6 : (vdata < n)) (PreH7 : (n <= INT_MAX)) (PreH8 : (rem = (cons (vdata) (rest)))) (PreH9 : (safeExec (pre_dfs2 (g_low_level_spec) (vis2_m) (sid_m)) (dfs_scc_from (root) (u) ((edges_of (u) (processed)))) X_low_level_spec )) ,
  (IntArray.full vis2 n vis2_m )
  **  (SllPtrArray.missing_i fadj n u head fadj_rows_low_level_spec )
  **  (sllseg head cur processed )
  **  ((&((cur)  # "list" ->ₛ "data")) # Int  |-> vdata)
  **  ((&((cur)  # "list" ->ₛ "next")) # Ptr  |-> next_ptr)
  **  (sll next_ptr rest )
  **  (IntArray.full sid n sid_m )
|--
  “ (vis2 = vis2_pre) ”
.

Definition dfs2_entail_wit_3_split_goal_14 := 
forall (sid_pre: Z) (fadj_rows_low_level_spec: (@list (@list Z))) (X_low_level_spec: (unit -> (KSt -> Prop))) (g_low_level_spec: AdjGraph) (head: Z) (processed: (@list Z)) (rem: (@list Z)) (vis2_m: (@list Z)) (sid_m: (@list Z)) (vdata: Z) (rest: (@list Z)) (next_ptr: Z) (cur: Z) (n: Z) (u: Z) (root: Z) (fadj: Z) (vis2: Z) (sid: Z) (PreH1 : (vdata <= INT_MAX)) (PreH2 : (vdata >= INT_MIN)) (PreH3 : ((Znth vdata vis2_m 0) = 0)) (PreH4 : (cur <> 0)) (PreH5 : (0 <= vdata)) (PreH6 : (vdata < n)) (PreH7 : (n <= INT_MAX)) (PreH8 : (rem = (cons (vdata) (rest)))) (PreH9 : (safeExec (pre_dfs2 (g_low_level_spec) (vis2_m) (sid_m)) (dfs_scc_from (root) (u) ((edges_of (u) (processed)))) X_low_level_spec )) ,
  (IntArray.full vis2 n vis2_m )
  **  (SllPtrArray.missing_i fadj n u head fadj_rows_low_level_spec )
  **  (sllseg head cur processed )
  **  ((&((cur)  # "list" ->ₛ "data")) # Int  |-> vdata)
  **  ((&((cur)  # "list" ->ₛ "next")) # Ptr  |-> next_ptr)
  **  (sll next_ptr rest )
  **  (IntArray.full sid n sid_m )
|--
  “ (sid = sid_pre) ”
.

Definition dfs2_entail_wit_3_split_goal_spatial := 
forall (sid_pre: Z) (vis2_pre: Z) (fadj_pre: Z) (n_pre: Z) (fadj_rows_low_level_spec: (@list (@list Z))) (X_low_level_spec: (unit -> (KSt -> Prop))) (g_low_level_spec: AdjGraph) (head: Z) (processed: (@list Z)) (rem: (@list Z)) (vis2_m: (@list Z)) (sid_m: (@list Z)) (vdata: Z) (rest: (@list Z)) (next_ptr: Z) (cur: Z) (n: Z) (u: Z) (root: Z) (fadj: Z) (vis2: Z) (sid: Z) (PreH1 : (vdata <= INT_MAX)) (PreH2 : (vdata >= INT_MIN)) (PreH3 : ((Znth vdata vis2_m 0) = 0)) (PreH4 : (cur <> 0)) (PreH5 : (0 <= vdata)) (PreH6 : (vdata < n)) (PreH7 : (n <= INT_MAX)) (PreH8 : (rem = (cons (vdata) (rest)))) (PreH9 : (safeExec (pre_dfs2 (g_low_level_spec) (vis2_m) (sid_m)) (dfs_scc_from (root) (u) ((edges_of (u) (processed)))) X_low_level_spec )) ,
  (IntArray.full vis2 n vis2_m )
  **  (SllPtrArray.missing_i fadj n u head fadj_rows_low_level_spec )
  **  (sllseg head cur processed )
  **  ((&((cur)  # "list" ->ₛ "data")) # Int  |-> vdata)
  **  ((&((cur)  # "list" ->ₛ "next")) # Ptr  |-> next_ptr)
  **  (sll next_ptr rest )
  **  (IntArray.full sid n sid_m )
|--
  (SllPtrArray.full fadj_pre n_pre fadj_rows_low_level_spec )
  **  (IntArray.full vis2_pre n_pre vis2_m )
  **  (IntArray.full sid_pre n_pre sid_m )
.

Definition dfs2_entail_wit_4_1 := 
(
forall (sid_pre: Z) (vis2_pre: Z) (fadj_pre: Z) (n_pre: Z) (u_pre: Z) (root_pre: Z) (fadj_rows_low_level_spec: (@list (@list Z))) (X_low_level_spec: (unit -> (KSt -> Prop))) (g_low_level_spec: AdjGraph) (head: Z) (processed: (@list Z)) (rem: (@list Z)) (vis2_m: (@list Z)) (sid_m: (@list Z)) (vdata: Z) (rest: (@list Z)) (next_ptr: Z) (cur: Z) (n: Z) (u: Z) (root: Z) (fadj: Z) (vis2: Z) (sid: Z) (PreH1 : ((Znth vdata vis2_m 0) <> 0)) (PreH2 : (cur <> 0)) (PreH3 : (0 <= vdata)) (PreH4 : (vdata < n)) (PreH5 : (n <= INT_MAX)) (PreH6 : (rem = (cons (vdata) (rest)))) (PreH7 : (safeExec (pre_dfs2 (g_low_level_spec) (vis2_m) (sid_m)) (dfs_scc_from (root) (u) ((edges_of (u) (processed)))) X_low_level_spec )) ,
  (IntArray.full vis2 n vis2_m )
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "u" ) )) # Int  |-> u)
  **  ((( &( "root" ) )) # Int  |-> root)
  **  ((( &( "fadj" ) )) # Ptr  |-> fadj)
  **  (SllPtrArray.missing_i fadj n u head fadj_rows_low_level_spec )
  **  (sllseg head cur processed )
  **  ((&((cur)  # "list" ->ₛ "data")) # Int  |-> vdata)
  **  ((&((cur)  # "list" ->ₛ "next")) # Ptr  |-> next_ptr)
  **  (sll next_ptr rest )
  **  ((( &( "vis2" ) )) # Ptr  |-> vis2)
  **  ((( &( "sid" ) )) # Ptr  |-> sid)
  **  (IntArray.full sid n sid_m )
|--
  EX (next_ptr_: Z)  (vis2_m_: (@list Z))  (sid_m_: (@list Z))  (rest_: (@list Z)) ,
  “ (cur <> 0) ” 
  &&  “ (0 <= root_pre) ” 
  &&  “ (root_pre < n_pre) ” 
  &&  “ (0 <= u_pre) ” 
  &&  “ (u_pre < n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (rem = (cons (vdata) (rest_))) ” 
  &&  “ (safeExec (pre_dfs2 (g_low_level_spec) (vis2_m_) (sid_m_)) (dfs_scc_from (root_pre) (u_pre) ((edges_of (u_pre) (processed)))) X_low_level_spec ) ”
  &&  ((( &( "root" ) )) # Int  |-> root_pre)
  **  ((( &( "u" ) )) # Int  |-> u_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "fadj" ) )) # Ptr  |-> fadj_pre)
  **  ((( &( "vis2" ) )) # Ptr  |-> vis2_pre)
  **  ((( &( "sid" ) )) # Ptr  |-> sid_pre)
  **  (SllPtrArray.missing_i fadj_pre n_pre u_pre head fadj_rows_low_level_spec )
  **  (sllseg head cur processed )
  **  ((&((cur)  # "list" ->ₛ "data")) # Int  |-> vdata)
  **  ((&((cur)  # "list" ->ₛ "next")) # Ptr  |-> next_ptr_)
  **  (sll next_ptr_ rest_ )
  **  (IntArray.full vis2_pre n_pre vis2_m_ )
  **  (IntArray.full sid_pre n_pre sid_m_ )
) \/
(
forall (sid_pre: Z) (vis2_pre: Z) (fadj_pre: Z) (n_pre: Z) (u_pre: Z) (root_pre: Z) (fadj_rows_low_level_spec: (@list (@list Z))) (X_low_level_spec: (unit -> (KSt -> Prop))) (g_low_level_spec: AdjGraph) (head: Z) (processed: (@list Z)) (rem: (@list Z)) (vis2_m: (@list Z)) (sid_m: (@list Z)) (vdata: Z) (rest: (@list Z)) (cur: Z) (n: Z) (u: Z) (root: Z) (fadj: Z) (vis2: Z) (sid: Z) (PreH1 : ((Znth vdata vis2_m 0) <> 0)) (PreH2 : (cur <> 0)) (PreH3 : (0 <= vdata)) (PreH4 : (vdata < n)) (PreH5 : (n <= INT_MAX)) (PreH6 : (rem = (cons (vdata) (rest)))) (PreH7 : (safeExec (pre_dfs2 (g_low_level_spec) (vis2_m) (sid_m)) (dfs_scc_from (root) (u) ((edges_of (u) (processed)))) X_low_level_spec )) ,
  (IntArray.full vis2 n vis2_m )
  **  (SllPtrArray.missing_i fadj n u head fadj_rows_low_level_spec )
  **  (sllseg head cur processed )
  **  (IntArray.full sid n sid_m )
|--
  EX (vis2_m_: (@list Z))  (sid_m_: (@list Z)) ,
  “ (sid = sid_pre) ” 
  &&  “ (vis2 = vis2_pre) ” 
  &&  “ (fadj = fadj_pre) ” 
  &&  “ (root = root_pre) ” 
  &&  “ (u = u_pre) ” 
  &&  “ (n = n_pre) ” 
  &&  “ (cur <> 0) ” 
  &&  “ (0 <= root_pre) ” 
  &&  “ (root_pre < n_pre) ” 
  &&  “ (0 <= u_pre) ” 
  &&  “ (u_pre < n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (rem = (cons (vdata) (rest))) ” 
  &&  “ (safeExec (pre_dfs2 (g_low_level_spec) (vis2_m_) (sid_m_)) (dfs_scc_from (root_pre) (u_pre) ((edges_of (u_pre) (processed)))) X_low_level_spec ) ”
  &&  (SllPtrArray.missing_i fadj_pre n_pre u_pre head fadj_rows_low_level_spec )
  **  (sllseg head cur processed )
  **  (IntArray.full vis2_pre n_pre vis2_m_ )
  **  (IntArray.full sid_pre n_pre sid_m_ )
).

Definition dfs2_entail_wit_4_2 := 
(
forall (sid_pre: Z) (vis2_pre: Z) (fadj_pre: Z) (n_pre: Z) (u_pre: Z) (root_pre: Z) (fadj_rows_low_level_spec: (@list (@list Z))) (X_low_level_spec: (unit -> (KSt -> Prop))) (g_low_level_spec: AdjGraph) (head: Z) (processed: (@list Z)) (rem: (@list Z)) (vis2_m: (@list Z)) (cur: Z) (v: Z) (vis2_l_: (@list Z)) (sid_l_: (@list Z)) (PreH1 : (safeExec (pre_dfs2 (g_low_level_spec) (vis2_l_) (sid_l_)) (return (tt)) X_low_level_spec )) (PreH2 : (cur <> 0)) (PreH3 : (0 <= root_pre)) (PreH4 : (root_pre < n_pre)) (PreH5 : (0 <= u_pre)) (PreH6 : (u_pre < n_pre)) (PreH7 : (0 <= v)) (PreH8 : (v < n_pre)) (PreH9 : (n_pre <= INT_MAX)) (PreH10 : ((Znth (v) (vis2_m) (0)) = 0)) ,
  (SllPtrArray.full fadj_pre n_pre fadj_rows_low_level_spec )
  **  (IntArray.full vis2_pre n_pre vis2_l_ )
  **  (IntArray.full sid_pre n_pre sid_l_ )
|--
  EX (next_ptr_: Z)  (vis2_m_: (@list Z))  (sid_m_: (@list Z))  (rest_: (@list Z)) ,
  “ (cur <> 0) ” 
  &&  “ (0 <= root_pre) ” 
  &&  “ (root_pre < n_pre) ” 
  &&  “ (0 <= u_pre) ” 
  &&  “ (u_pre < n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (rem = (cons (v) (rest_))) ” 
  &&  “ (safeExec (pre_dfs2 (g_low_level_spec) (vis2_m_) (sid_m_)) (dfs_scc_from (root_pre) (u_pre) ((edges_of (u_pre) (processed)))) X_low_level_spec ) ”
  &&  (SllPtrArray.missing_i fadj_pre n_pre u_pre head fadj_rows_low_level_spec )
  **  (sllseg head cur processed )
  **  ((&((cur)  # "list" ->ₛ "data")) # Int  |-> v)
  **  ((&((cur)  # "list" ->ₛ "next")) # Ptr  |-> next_ptr_)
  **  (sll next_ptr_ rest_ )
  **  (IntArray.full vis2_pre n_pre vis2_m_ )
  **  (IntArray.full sid_pre n_pre sid_m_ )
) \/
(
forall (fadj_pre: Z) (n_pre: Z) (u_pre: Z) (root_pre: Z) (fadj_rows_low_level_spec: (@list (@list Z))) (X_low_level_spec: (unit -> (KSt -> Prop))) (g_low_level_spec: AdjGraph) (head: Z) (processed: (@list Z)) (rem: (@list Z)) (vis2_m: (@list Z)) (cur: Z) (v: Z) (vis2_l_: (@list Z)) (sid_l_: (@list Z)) (PreH1 : (safeExec (pre_dfs2 (g_low_level_spec) (vis2_l_) (sid_l_)) (return (tt)) X_low_level_spec )) (PreH2 : (cur <> 0)) (PreH3 : (0 <= root_pre)) (PreH4 : (root_pre < n_pre)) (PreH5 : (0 <= u_pre)) (PreH6 : (u_pre < n_pre)) (PreH7 : (0 <= v)) (PreH8 : (v < n_pre)) (PreH9 : (n_pre <= INT_MAX)) (PreH10 : ((Znth (v) (vis2_m) (0)) = 0)) ,
  (SllPtrArray.full fadj_pre n_pre fadj_rows_low_level_spec )
|--
  EX (next_ptr_: Z)  (rest_: (@list Z)) ,
  “ (cur <> 0) ” 
  &&  “ (0 <= root_pre) ” 
  &&  “ (root_pre < n_pre) ” 
  &&  “ (0 <= u_pre) ” 
  &&  “ (u_pre < n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (rem = (cons (v) (rest_))) ” 
  &&  “ (safeExec (pre_dfs2 (g_low_level_spec) (vis2_l_) (sid_l_)) (dfs_scc_from (root_pre) (u_pre) ((edges_of (u_pre) (processed)))) X_low_level_spec ) ”
  &&  (SllPtrArray.missing_i fadj_pre n_pre u_pre head fadj_rows_low_level_spec )
  **  (sllseg head cur processed )
  **  ((&((cur)  # "list" ->ₛ "data")) # Int  |-> v)
  **  ((&((cur)  # "list" ->ₛ "next")) # Ptr  |-> next_ptr_)
  **  (sll next_ptr_ rest_ )
).

Definition dfs2_entail_wit_5 := 
(
forall (sid_pre: Z) (vis2_pre: Z) (fadj_pre: Z) (n_pre: Z) (u_pre: Z) (root_pre: Z) (fadj_rows_low_level_spec: (@list (@list Z))) (X_low_level_spec: (unit -> (KSt -> Prop))) (g_low_level_spec: AdjGraph) (head_2: Z) (processed_2: (@list Z)) (rem_2: (@list Z)) (vdata_: Z) (rest_: (@list Z)) (next_ptr_: Z) (vis2_m_: (@list Z)) (sid_m_: (@list Z)) (cur: Z) (PreH1 : (cur <> 0)) (PreH2 : (0 <= root_pre)) (PreH3 : (root_pre < n_pre)) (PreH4 : (0 <= u_pre)) (PreH5 : (u_pre < n_pre)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : (rem_2 = (cons (vdata_) (rest_)))) (PreH8 : (safeExec (pre_dfs2 (g_low_level_spec) (vis2_m_) (sid_m_)) (dfs_scc_from (root_pre) (u_pre) ((edges_of (u_pre) (processed_2)))) X_low_level_spec )) ,
  (SllPtrArray.missing_i fadj_pre n_pre u_pre head_2 fadj_rows_low_level_spec )
  **  (sllseg head_2 cur processed_2 )
  **  ((&((cur)  # "list" ->ₛ "data")) # Int  |-> vdata_)
  **  ((&((cur)  # "list" ->ₛ "next")) # Ptr  |-> next_ptr_)
  **  (sll next_ptr_ rest_ )
  **  (IntArray.full vis2_pre n_pre vis2_m_ )
  **  (IntArray.full sid_pre n_pre sid_m_ )
|--
  EX (rem: (@list Z))  (head: Z)  (vis2_m: (@list Z))  (sid_m: (@list Z))  (processed: (@list Z)) ,
  “ (safeExec (pre_dfs2 (g_low_level_spec) (vis2_m) (sid_m)) (dfs_scc_from (root_pre) (u_pre) ((edges_of (u_pre) (processed)))) X_low_level_spec ) ” 
  &&  “ (0 <= root_pre) ” 
  &&  “ (root_pre < n_pre) ” 
  &&  “ (0 <= u_pre) ” 
  &&  “ (u_pre < n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ”
  &&  (SllPtrArray.missing_i fadj_pre n_pre u_pre head fadj_rows_low_level_spec )
  **  (sllseg head next_ptr_ processed )
  **  (sll next_ptr_ rem )
  **  (IntArray.full vis2_pre n_pre vis2_m )
  **  (IntArray.full sid_pre n_pre sid_m )
) \/
(
forall (fadj_pre: Z) (n_pre: Z) (u_pre: Z) (root_pre: Z) (fadj_rows_low_level_spec: (@list (@list Z))) (X_low_level_spec: (unit -> (KSt -> Prop))) (g_low_level_spec: AdjGraph) (head_2: Z) (processed_2: (@list Z)) (rem_2: (@list Z)) (vdata_: Z) (rest_: (@list Z)) (next_ptr_: Z) (vis2_m_: (@list Z)) (sid_m_: (@list Z)) (cur: Z) (PreH1 : (vdata_ <= INT_MAX)) (PreH2 : (vdata_ >= INT_MIN)) (PreH3 : (cur <> 0)) (PreH4 : (0 <= root_pre)) (PreH5 : (root_pre < n_pre)) (PreH6 : (0 <= u_pre)) (PreH7 : (u_pre < n_pre)) (PreH8 : (n_pre <= INT_MAX)) (PreH9 : (rem_2 = (cons (vdata_) (rest_)))) (PreH10 : (safeExec (pre_dfs2 (g_low_level_spec) (vis2_m_) (sid_m_)) (dfs_scc_from (root_pre) (u_pre) ((edges_of (u_pre) (processed_2)))) X_low_level_spec )) ,
  (SllPtrArray.missing_i fadj_pre n_pre u_pre head_2 fadj_rows_low_level_spec )
  **  (sllseg head_2 cur processed_2 )
  **  ((&((cur)  # "list" ->ₛ "data")) # Int  |-> vdata_)
  **  ((&((cur)  # "list" ->ₛ "next")) # Ptr  |-> next_ptr_)
|--
  EX (head: Z)  (processed: (@list Z)) ,
  “ (safeExec (pre_dfs2 (g_low_level_spec) (vis2_m_) (sid_m_)) (dfs_scc_from (root_pre) (u_pre) ((edges_of (u_pre) (processed)))) X_low_level_spec ) ” 
  &&  “ (0 <= root_pre) ” 
  &&  “ (root_pre < n_pre) ” 
  &&  “ (0 <= u_pre) ” 
  &&  “ (u_pre < n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ”
  &&  (SllPtrArray.missing_i fadj_pre n_pre u_pre head fadj_rows_low_level_spec )
  **  (sllseg head next_ptr_ processed )
).

Definition dfs2_entail_wit_6 := 
(
forall (sid_pre: Z) (vis2_pre: Z) (fadj_pre: Z) (n_pre: Z) (u_pre: Z) (root_pre: Z) (fadj_rows_low_level_spec: (@list (@list Z))) (X_low_level_spec: (unit -> (KSt -> Prop))) (g_low_level_spec: AdjGraph) (rem: (@list Z)) (cur: Z) (head_2: Z) (vis2_m_2: (@list Z)) (sid_m_2: (@list Z)) (processed: (@list Z)) (PreH1 : (cur = 0)) (PreH2 : (safeExec (pre_dfs2 (g_low_level_spec) (vis2_m_2) (sid_m_2)) (dfs_scc_from (root_pre) (u_pre) ((edges_of (u_pre) (processed)))) X_low_level_spec )) (PreH3 : (0 <= root_pre)) (PreH4 : (root_pre < n_pre)) (PreH5 : (0 <= u_pre)) (PreH6 : (u_pre < n_pre)) (PreH7 : (n_pre <= INT_MAX)) ,
  (SllPtrArray.missing_i fadj_pre n_pre u_pre head_2 fadj_rows_low_level_spec )
  **  ((( &( "cur" ) )) # Ptr  |-> cur)
  **  (sllseg head_2 cur processed )
  **  (sll cur rem )
  **  (IntArray.full vis2_pre n_pre vis2_m_2 )
  **  (IntArray.full sid_pre n_pre sid_m_2 )
|--
  EX (head: Z)  (vis2_m: (@list Z))  (sid_m: (@list Z)) ,
  “ (0 <= root_pre) ” 
  &&  “ (root_pre < n_pre) ” 
  &&  “ (0 <= u_pre) ” 
  &&  “ (u_pre < n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (safeExec (pre_dfs2 (g_low_level_spec) (vis2_m) (sid_m)) (return (tt)) X_low_level_spec ) ”
  &&  (SllPtrArray.missing_i fadj_pre n_pre u_pre head fadj_rows_low_level_spec )
  **  (sll head (Znth (u_pre) (fadj_rows_low_level_spec) ((@nil Z))) )
  **  ((( &( "cur" ) )) # Ptr  |-> 0)
  **  (IntArray.full vis2_pre n_pre vis2_m )
  **  (IntArray.full sid_pre n_pre sid_m )
) \/
(
forall (fadj_pre: Z) (n_pre: Z) (u_pre: Z) (root_pre: Z) (fadj_rows_low_level_spec: (@list (@list Z))) (X_low_level_spec: (unit -> (KSt -> Prop))) (g_low_level_spec: AdjGraph) (rem: (@list Z)) (cur: Z) (head_2: Z) (vis2_m_2: (@list Z)) (sid_m_2: (@list Z)) (processed: (@list Z)) (PreH1 : (cur = 0)) (PreH2 : (safeExec (pre_dfs2 (g_low_level_spec) (vis2_m_2) (sid_m_2)) (dfs_scc_from (root_pre) (u_pre) ((edges_of (u_pre) (processed)))) X_low_level_spec )) (PreH3 : (0 <= root_pre)) (PreH4 : (root_pre < n_pre)) (PreH5 : (0 <= u_pre)) (PreH6 : (u_pre < n_pre)) (PreH7 : (n_pre <= INT_MAX)) ,
  (SllPtrArray.missing_i fadj_pre n_pre u_pre head_2 fadj_rows_low_level_spec )
  **  (sllseg head_2 cur processed )
  **  (sll cur rem )
|--
  EX (head: Z) ,
  “ (cur = 0) ” 
  &&  “ (0 <= root_pre) ” 
  &&  “ (root_pre < n_pre) ” 
  &&  “ (0 <= u_pre) ” 
  &&  “ (u_pre < n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (safeExec (pre_dfs2 (g_low_level_spec) (vis2_m_2) (sid_m_2)) (return (tt)) X_low_level_spec ) ”
  &&  (SllPtrArray.missing_i fadj_pre n_pre u_pre head fadj_rows_low_level_spec )
  **  (sll head (Znth (u_pre) (fadj_rows_low_level_spec) ((@nil Z))) )
).

Definition dfs2_return_wit_1 := 
(
forall (sid_pre: Z) (vis2_pre: Z) (fadj_pre: Z) (n_pre: Z) (u_pre: Z) (root_pre: Z) (fadj_rows_low_level_spec: (@list (@list Z))) (X_low_level_spec: (unit -> (KSt -> Prop))) (g_low_level_spec: AdjGraph) (head: Z) (vis2_m: (@list Z)) (sid_m: (@list Z)) (PreH1 : (0 <= root_pre)) (PreH2 : (root_pre < n_pre)) (PreH3 : (0 <= u_pre)) (PreH4 : (u_pre < n_pre)) (PreH5 : (n_pre <= INT_MAX)) (PreH6 : (safeExec (pre_dfs2 (g_low_level_spec) (vis2_m) (sid_m)) (return (tt)) X_low_level_spec )) ,
  (SllPtrArray.missing_i fadj_pre n_pre u_pre head fadj_rows_low_level_spec )
  **  (sll head (Znth (u_pre) (fadj_rows_low_level_spec) ((@nil Z))) )
  **  (IntArray.full vis2_pre n_pre vis2_m )
  **  (IntArray.full sid_pre n_pre sid_m )
|--
  EX (vis2_l_: (@list Z))  (sid_l_: (@list Z)) ,
  “ (safeExec (pre_dfs2 (g_low_level_spec) (vis2_l_) (sid_l_)) (return (tt)) X_low_level_spec ) ”
  &&  (SllPtrArray.full fadj_pre n_pre fadj_rows_low_level_spec )
  **  (IntArray.full vis2_pre n_pre vis2_l_ )
  **  (IntArray.full sid_pre n_pre sid_l_ )
) \/
(
forall (fadj_pre: Z) (n_pre: Z) (u_pre: Z) (root_pre: Z) (fadj_rows_low_level_spec: (@list (@list Z))) (X_low_level_spec: (unit -> (KSt -> Prop))) (g_low_level_spec: AdjGraph) (head: Z) (vis2_m: (@list Z)) (sid_m: (@list Z)) (PreH1 : (0 <= root_pre)) (PreH2 : (root_pre < n_pre)) (PreH3 : (0 <= u_pre)) (PreH4 : (u_pre < n_pre)) (PreH5 : (n_pre <= INT_MAX)) (PreH6 : (safeExec (pre_dfs2 (g_low_level_spec) (vis2_m) (sid_m)) (return (tt)) X_low_level_spec )) ,
  (SllPtrArray.missing_i fadj_pre n_pre u_pre head fadj_rows_low_level_spec )
  **  (sll head (Znth (u_pre) (fadj_rows_low_level_spec) ((@nil Z))) )
|--
  (SllPtrArray.full fadj_pre n_pre fadj_rows_low_level_spec )
).

Definition dfs2_return_wit_1_split_goal_spatial := 
forall (fadj_pre: Z) (n_pre: Z) (u_pre: Z) (root_pre: Z) (fadj_rows_low_level_spec: (@list (@list Z))) (X_low_level_spec: (unit -> (KSt -> Prop))) (g_low_level_spec: AdjGraph) (head: Z) (vis2_m: (@list Z)) (sid_m: (@list Z)) (PreH1 : (0 <= root_pre)) (PreH2 : (root_pre < n_pre)) (PreH3 : (0 <= u_pre)) (PreH4 : (u_pre < n_pre)) (PreH5 : (n_pre <= INT_MAX)) (PreH6 : (safeExec (pre_dfs2 (g_low_level_spec) (vis2_m) (sid_m)) (return (tt)) X_low_level_spec )) ,
  (SllPtrArray.missing_i fadj_pre n_pre u_pre head fadj_rows_low_level_spec )
  **  (sll head (Znth (u_pre) (fadj_rows_low_level_spec) ((@nil Z))) )
|--
  (SllPtrArray.full fadj_pre n_pre fadj_rows_low_level_spec )
.

Definition dfs2_partial_solve_wit_1 := 
forall (sid_pre: Z) (vis2_pre: Z) (fadj_pre: Z) (n_pre: Z) (u_pre: Z) (root_pre: Z) (fadj_rows_low_level_spec: (@list (@list Z))) (X_low_level_spec: (unit -> (KSt -> Prop))) (sid_l_low_level_spec: (@list Z)) (vis2_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (PreH1 : (safeExec (pre_dfs2 (g_low_level_spec) (vis2_l_low_level_spec) (sid_l_low_level_spec)) (dfs_scc (root_pre) (u_pre)) X_low_level_spec )) (PreH2 : (0 <= root_pre)) (PreH3 : (root_pre < n_pre)) (PreH4 : (0 <= u_pre)) (PreH5 : (u_pre < n_pre)) (PreH6 : (n_pre <= INT_MAX)) ,
  (SllPtrArray.full fadj_pre n_pre fadj_rows_low_level_spec )
  **  (IntArray.full vis2_pre n_pre vis2_l_low_level_spec )
  **  (IntArray.full sid_pre n_pre sid_l_low_level_spec )
|--
  “ (safeExec (pre_dfs2 (g_low_level_spec) (vis2_l_low_level_spec) (sid_l_low_level_spec)) (dfs_scc (root_pre) (u_pre)) X_low_level_spec ) ” 
  &&  “ (0 <= root_pre) ” 
  &&  “ (root_pre < n_pre) ” 
  &&  “ (0 <= u_pre) ” 
  &&  “ (u_pre < n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ”
  &&  (((vis2_pre + (u_pre * sizeof(INT) ) )) # Int  |->_)
  **  (IntArray.missing_i vis2_pre u_pre 0 n_pre vis2_l_low_level_spec )
  **  (SllPtrArray.full fadj_pre n_pre fadj_rows_low_level_spec )
  **  (IntArray.full sid_pre n_pre sid_l_low_level_spec )
.

Definition dfs2_partial_solve_wit_2 := 
forall (sid_pre: Z) (vis2_pre: Z) (fadj_pre: Z) (n_pre: Z) (u_pre: Z) (root_pre: Z) (fadj_rows_low_level_spec: (@list (@list Z))) (X_low_level_spec: (unit -> (KSt -> Prop))) (sid_l_low_level_spec: (@list Z)) (vis2_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (PreH1 : (safeExec (pre_dfs2 (g_low_level_spec) (vis2_l_low_level_spec) (sid_l_low_level_spec)) (dfs_scc (root_pre) (u_pre)) X_low_level_spec )) (PreH2 : (0 <= root_pre)) (PreH3 : (root_pre < n_pre)) (PreH4 : (0 <= u_pre)) (PreH5 : (u_pre < n_pre)) (PreH6 : (n_pre <= INT_MAX)) ,
  (IntArray.full vis2_pre n_pre (replace_Znth (u_pre) (1) (vis2_l_low_level_spec)) )
  **  (SllPtrArray.full fadj_pre n_pre fadj_rows_low_level_spec )
  **  (IntArray.full sid_pre n_pre sid_l_low_level_spec )
|--
  “ (safeExec (pre_dfs2 (g_low_level_spec) (vis2_l_low_level_spec) (sid_l_low_level_spec)) (dfs_scc (root_pre) (u_pre)) X_low_level_spec ) ” 
  &&  “ (0 <= root_pre) ” 
  &&  “ (root_pre < n_pre) ” 
  &&  “ (0 <= u_pre) ” 
  &&  “ (u_pre < n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ”
  &&  (((sid_pre + (root_pre * sizeof(INT) ) )) # Int  |-> (Znth root_pre sid_l_low_level_spec 0))
  **  (IntArray.missing_i sid_pre root_pre 0 n_pre sid_l_low_level_spec )
  **  (IntArray.full vis2_pre n_pre (replace_Znth (u_pre) (1) (vis2_l_low_level_spec)) )
  **  (SllPtrArray.full fadj_pre n_pre fadj_rows_low_level_spec )
.

Definition dfs2_partial_solve_wit_3 := 
forall (sid_pre: Z) (vis2_pre: Z) (fadj_pre: Z) (n_pre: Z) (u_pre: Z) (root_pre: Z) (fadj_rows_low_level_spec: (@list (@list Z))) (X_low_level_spec: (unit -> (KSt -> Prop))) (sid_l_low_level_spec: (@list Z)) (vis2_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (PreH1 : (safeExec (pre_dfs2 (g_low_level_spec) (vis2_l_low_level_spec) (sid_l_low_level_spec)) (dfs_scc (root_pre) (u_pre)) X_low_level_spec )) (PreH2 : (0 <= root_pre)) (PreH3 : (root_pre < n_pre)) (PreH4 : (0 <= u_pre)) (PreH5 : (u_pre < n_pre)) (PreH6 : (n_pre <= INT_MAX)) ,
  (IntArray.full sid_pre n_pre sid_l_low_level_spec )
  **  (IntArray.full vis2_pre n_pre (replace_Znth (u_pre) (1) (vis2_l_low_level_spec)) )
  **  (SllPtrArray.full fadj_pre n_pre fadj_rows_low_level_spec )
|--
  “ (safeExec (pre_dfs2 (g_low_level_spec) (vis2_l_low_level_spec) (sid_l_low_level_spec)) (dfs_scc (root_pre) (u_pre)) X_low_level_spec ) ” 
  &&  “ (0 <= root_pre) ” 
  &&  “ (root_pre < n_pre) ” 
  &&  “ (0 <= u_pre) ” 
  &&  “ (u_pre < n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ”
  &&  (((sid_pre + (u_pre * sizeof(INT) ) )) # Int  |->_)
  **  (IntArray.missing_i sid_pre u_pre 0 n_pre sid_l_low_level_spec )
  **  (IntArray.full vis2_pre n_pre (replace_Znth (u_pre) (1) (vis2_l_low_level_spec)) )
  **  (SllPtrArray.full fadj_pre n_pre fadj_rows_low_level_spec )
.

Definition dfs2_partial_solve_wit_4 := 
forall (sid_pre: Z) (vis2_pre: Z) (fadj_pre: Z) (n_pre: Z) (u_pre: Z) (root_pre: Z) (fadj_rows_low_level_spec: (@list (@list Z))) (X_low_level_spec: (unit -> (KSt -> Prop))) (sid_l_low_level_spec: (@list Z)) (vis2_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph)  __default__List_Z (PreH1 : (safeExec (pre_dfs2 (g_low_level_spec) (vis2_l_low_level_spec) (sid_l_low_level_spec)) (dfs_scc (root_pre) (u_pre)) X_low_level_spec )) (PreH2 : (0 <= root_pre)) (PreH3 : (root_pre < n_pre)) (PreH4 : (0 <= u_pre)) (PreH5 : (u_pre < n_pre)) (PreH6 : (n_pre <= INT_MAX)) ,
  (IntArray.full sid_pre n_pre (replace_Znth (u_pre) ((Znth root_pre sid_l_low_level_spec 0)) (sid_l_low_level_spec)) )
  **  (IntArray.full vis2_pre n_pre (replace_Znth (u_pre) (1) (vis2_l_low_level_spec)) )
  **  (SllPtrArray.full fadj_pre n_pre fadj_rows_low_level_spec )
|--
  EX (row_ptr: Z) ,
  “ (safeExec (pre_dfs2 (g_low_level_spec) (vis2_l_low_level_spec) (sid_l_low_level_spec)) (dfs_scc (root_pre) (u_pre)) X_low_level_spec ) ” 
  &&  “ (0 <= root_pre) ” 
  &&  “ (root_pre < n_pre) ” 
  &&  “ (0 <= u_pre) ” 
  &&  “ (u_pre < n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ”
  &&  (((fadj_pre + (u_pre * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (sll row_ptr (Znth u_pre fadj_rows_low_level_spec __default__List_Z) )
  **  (SllPtrArray.missing_i fadj_pre n_pre u_pre row_ptr fadj_rows_low_level_spec )
  **  (IntArray.full sid_pre n_pre (replace_Znth (u_pre) ((Znth root_pre sid_l_low_level_spec 0)) (sid_l_low_level_spec)) )
  **  (IntArray.full vis2_pre n_pre (replace_Znth (u_pre) (1) (vis2_l_low_level_spec)) )
.

Definition dfs2_partial_solve_wit_5 := 
forall (fadj_rows_low_level_spec: (@list (@list Z))) (X_low_level_spec: (unit -> (KSt -> Prop))) (g_low_level_spec: AdjGraph) (head: Z) (processed: (@list Z)) (rem: (@list Z)) (vis2_m: (@list Z)) (sid_m: (@list Z)) (vdata: Z) (rest: (@list Z)) (next_ptr: Z) (cur: Z) (n: Z) (u: Z) (root: Z) (fadj: Z) (vis2: Z) (sid: Z) (PreH1 : (cur <> 0)) (PreH2 : (0 <= vdata)) (PreH3 : (vdata < n)) (PreH4 : (n <= INT_MAX)) (PreH5 : (rem = (cons (vdata) (rest)))) (PreH6 : (safeExec (pre_dfs2 (g_low_level_spec) (vis2_m) (sid_m)) (dfs_scc_from (root) (u) ((edges_of (u) (processed)))) X_low_level_spec )) ,
  (SllPtrArray.missing_i fadj n u head fadj_rows_low_level_spec )
  **  (sllseg head cur processed )
  **  ((&((cur)  # "list" ->ₛ "data")) # Int  |-> vdata)
  **  ((&((cur)  # "list" ->ₛ "next")) # Ptr  |-> next_ptr)
  **  (sll next_ptr rest )
  **  (IntArray.full vis2 n vis2_m )
  **  (IntArray.full sid n sid_m )
|--
  “ (cur <> 0) ” 
  &&  “ (0 <= vdata) ” 
  &&  “ (vdata < n) ” 
  &&  “ (n <= INT_MAX) ” 
  &&  “ (rem = (cons (vdata) (rest))) ” 
  &&  “ (safeExec (pre_dfs2 (g_low_level_spec) (vis2_m) (sid_m)) (dfs_scc_from (root) (u) ((edges_of (u) (processed)))) X_low_level_spec ) ”
  &&  (((vis2 + (vdata * sizeof(INT) ) )) # Int  |-> (Znth vdata vis2_m 0))
  **  (IntArray.missing_i vis2 vdata 0 n vis2_m )
  **  (SllPtrArray.missing_i fadj n u head fadj_rows_low_level_spec )
  **  (sllseg head cur processed )
  **  ((&((cur)  # "list" ->ₛ "data")) # Int  |-> vdata)
  **  ((&((cur)  # "list" ->ₛ "next")) # Ptr  |-> next_ptr)
  **  (sll next_ptr rest )
  **  (IntArray.full sid n sid_m )
.

Definition dfs2_partial_solve_wit_6_pure := 
forall (sid_pre: Z) (vis2_pre: Z) (fadj_pre: Z) (n_pre: Z) (u_pre: Z) (root_pre: Z) (fadj_rows_low_level_spec: (@list (@list Z))) (X_low_level_spec: (unit -> (KSt -> Prop))) (g_low_level_spec: AdjGraph) (vis2_m: (@list Z)) (sid_m: (@list Z)) (cur: Z) (v: Z) (PreH1 : (cur <> 0)) (PreH2 : (0 <= root_pre)) (PreH3 : (root_pre < n_pre)) (PreH4 : (0 <= u_pre)) (PreH5 : (u_pre < n_pre)) (PreH6 : (0 <= v)) (PreH7 : (v < n_pre)) (PreH8 : (n_pre <= INT_MAX)) (PreH9 : ((Znth (v) (vis2_m) (0)) = 0)) (PreH10 : (safeExec (pre_dfs2 (g_low_level_spec) (vis2_m) (sid_m)) (dfs_scc (root_pre) (v)) X_low_level_spec )) ,
  ((( &( "root" ) )) # Int  |-> root_pre)
  **  ((( &( "u" ) )) # Int  |-> u_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "fadj" ) )) # Ptr  |-> fadj_pre)
  **  ((( &( "vis2" ) )) # Ptr  |-> vis2_pre)
  **  ((( &( "sid" ) )) # Ptr  |-> sid_pre)
  **  ((( &( "cur" ) )) # Ptr  |-> cur)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  (SllPtrArray.full fadj_pre n_pre fadj_rows_low_level_spec )
  **  (IntArray.full vis2_pre n_pre vis2_m )
  **  (IntArray.full sid_pre n_pre sid_m )
|--
  “ (safeExec (pre_dfs2 (g_low_level_spec) (vis2_m) (sid_m)) (dfs_scc (root_pre) (v)) X_low_level_spec ) ” 
  &&  “ (0 <= root_pre) ” 
  &&  “ (root_pre < n_pre) ” 
  &&  “ (0 <= v) ” 
  &&  “ (v < n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ”
.

Definition dfs2_partial_solve_wit_6_aux := 
forall (sid_pre: Z) (vis2_pre: Z) (fadj_pre: Z) (n_pre: Z) (u_pre: Z) (root_pre: Z) (fadj_rows_low_level_spec: (@list (@list Z))) (X_low_level_spec: (unit -> (KSt -> Prop))) (g_low_level_spec: AdjGraph) (vis2_m: (@list Z)) (sid_m: (@list Z)) (cur: Z) (v: Z) (PreH1 : (cur <> 0)) (PreH2 : (0 <= root_pre)) (PreH3 : (root_pre < n_pre)) (PreH4 : (0 <= u_pre)) (PreH5 : (u_pre < n_pre)) (PreH6 : (0 <= v)) (PreH7 : (v < n_pre)) (PreH8 : (n_pre <= INT_MAX)) (PreH9 : ((Znth (v) (vis2_m) (0)) = 0)) (PreH10 : (safeExec (pre_dfs2 (g_low_level_spec) (vis2_m) (sid_m)) (dfs_scc (root_pre) (v)) X_low_level_spec )) ,
  (SllPtrArray.full fadj_pre n_pre fadj_rows_low_level_spec )
  **  (IntArray.full vis2_pre n_pre vis2_m )
  **  (IntArray.full sid_pre n_pre sid_m )
|--
  “ (safeExec (pre_dfs2 (g_low_level_spec) (vis2_m) (sid_m)) (dfs_scc (root_pre) (v)) X_low_level_spec ) ” 
  &&  “ (0 <= root_pre) ” 
  &&  “ (root_pre < n_pre) ” 
  &&  “ (0 <= v) ” 
  &&  “ (v < n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (cur <> 0) ” 
  &&  “ (0 <= root_pre) ” 
  &&  “ (root_pre < n_pre) ” 
  &&  “ (0 <= u_pre) ” 
  &&  “ (u_pre < n_pre) ” 
  &&  “ (0 <= v) ” 
  &&  “ (v < n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ ((Znth (v) (vis2_m) (0)) = 0) ” 
  &&  “ (safeExec (pre_dfs2 (g_low_level_spec) (vis2_m) (sid_m)) (dfs_scc (root_pre) (v)) X_low_level_spec ) ”
  &&  (SllPtrArray.full fadj_pre n_pre fadj_rows_low_level_spec )
  **  (IntArray.full vis2_pre n_pre vis2_m )
  **  (IntArray.full sid_pre n_pre sid_m )
.

Definition dfs2_partial_solve_wit_6 := dfs2_partial_solve_wit_6_pure -> dfs2_partial_solve_wit_6_aux.

(*----- Function kosaraju_finish -----*)

Definition kosaraju_finish_safety_wit_1 := 
forall (timer_p_pre: Z) (fin_pre: Z) (vis1_pre: Z) (radj_pre: Z) (n_pre: Z) (radj_rows_low_level_spec: (@list (@list Z))) (X_low_level_spec: (unit -> (KSt -> Prop))) (scc_next_v_abs_low_level_spec: Z) (timer_v_low_level_spec: Z) (sid_l_abs_low_level_spec: (@list Z)) (fin_l_low_level_spec: (@list Z)) (vis2_l_abs_low_level_spec: (@list Z)) (vis1_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (PreH1 : (safeExec (pre_kosaraju (g_low_level_spec) (vis1_l_low_level_spec) (vis2_l_abs_low_level_spec) (fin_l_low_level_spec) (sid_l_abs_low_level_spec) (timer_v_low_level_spec) (scc_next_v_abs_low_level_spec)) kosaraju_finish_monad X_low_level_spec )) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= INT_MAX)) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "timer_p" ) )) # Ptr  |-> timer_p_pre)
  **  ((( &( "fin" ) )) # Ptr  |-> fin_pre)
  **  ((( &( "vis1" ) )) # Ptr  |-> vis1_pre)
  **  ((( &( "radj" ) )) # Ptr  |-> radj_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (SllPtrArray.full radj_pre n_pre radj_rows_low_level_spec )
  **  (IntArray.full vis1_pre n_pre vis1_l_low_level_spec )
  **  (IntArray.full fin_pre n_pre fin_l_low_level_spec )
  **  (IntArray.full timer_p_pre 1 (cons (timer_v_low_level_spec) ((@nil Z))) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition kosaraju_finish_safety_wit_2 := 
forall (timer_p_pre: Z) (fin_pre: Z) (vis1_pre: Z) (radj_pre: Z) (n_pre: Z) (radj_rows_low_level_spec: (@list (@list Z))) (X_low_level_spec: (unit -> (KSt -> Prop))) (scc_next_v_abs_low_level_spec: Z) (sid_l_abs_low_level_spec: (@list Z)) (vis2_l_abs_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (vis1_m: (@list Z)) (fin_m: (@list Z)) (timer_m: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (safeExec (pre_kosaraju (g_low_level_spec) (vis1_m) (vis2_l_abs_low_level_spec) (fin_m) (sid_l_abs_low_level_spec) (timer_m) (scc_next_v_abs_low_level_spec)) (kosaraju_finish_from (i)) X_low_level_spec )) (PreH3 : (0 <= i)) (PreH4 : (i <= n_pre)) (PreH5 : (n_pre <= INT_MAX)) ,
  (IntArray.full vis1_pre n_pre vis1_m )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "radj" ) )) # Ptr  |-> radj_pre)
  **  ((( &( "vis1" ) )) # Ptr  |-> vis1_pre)
  **  ((( &( "fin" ) )) # Ptr  |-> fin_pre)
  **  ((( &( "timer_p" ) )) # Ptr  |-> timer_p_pre)
  **  (SllPtrArray.full radj_pre n_pre radj_rows_low_level_spec )
  **  (IntArray.full fin_pre n_pre fin_m )
  **  (IntArray.full timer_p_pre 1 (cons (timer_m) ((@nil Z))) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition kosaraju_finish_safety_wit_3 := 
forall (timer_p_pre: Z) (fin_pre: Z) (vis1_pre: Z) (radj_pre: Z) (n_pre: Z) (radj_rows_low_level_spec: (@list (@list Z))) (X_low_level_spec: (unit -> (KSt -> Prop))) (g_low_level_spec: AdjGraph) (vis1_m: (@list Z)) (i: Z) (vis1_l_: (@list Z)) (fin_l_: (@list Z)) (timer_v_: Z) (PreH1 : (safeExec (pre_dfs1 (g_low_level_spec) (vis1_l_) (fin_l_) (timer_v_)) (return (tt)) X_low_level_spec )) (PreH2 : (0 <= i)) (PreH3 : (i < n_pre)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : ((Znth (i) (vis1_m) (0)) = 0)) ,
  (SllPtrArray.full radj_pre n_pre radj_rows_low_level_spec )
  **  (IntArray.full vis1_pre n_pre vis1_l_ )
  **  (IntArray.full fin_pre n_pre fin_l_ )
  **  (IntArray.full timer_p_pre 1 (cons (timer_v_) ((@nil Z))) )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "radj" ) )) # Ptr  |-> radj_pre)
  **  ((( &( "vis1" ) )) # Ptr  |-> vis1_pre)
  **  ((( &( "fin" ) )) # Ptr  |-> fin_pre)
  **  ((( &( "timer_p" ) )) # Ptr  |-> timer_p_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition kosaraju_finish_safety_wit_4 := 
forall (timer_p_pre: Z) (fin_pre: Z) (vis1_pre: Z) (radj_pre: Z) (n_pre: Z) (radj_rows_low_level_spec: (@list (@list Z))) (X_low_level_spec: (unit -> (KSt -> Prop))) (scc_next_v_abs_low_level_spec: Z) (sid_l_abs_low_level_spec: (@list Z)) (vis2_l_abs_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (vis1_m: (@list Z)) (fin_m: (@list Z)) (timer_m: Z) (i: Z) (PreH1 : ((Znth i vis1_m 0) <> 0)) (PreH2 : (i < n_pre)) (PreH3 : (safeExec (pre_kosaraju (g_low_level_spec) (vis1_m) (vis2_l_abs_low_level_spec) (fin_m) (sid_l_abs_low_level_spec) (timer_m) (scc_next_v_abs_low_level_spec)) (kosaraju_finish_from (i)) X_low_level_spec )) (PreH4 : (0 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (n_pre <= INT_MAX)) ,
  (IntArray.full vis1_pre n_pre vis1_m )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "radj" ) )) # Ptr  |-> radj_pre)
  **  ((( &( "vis1" ) )) # Ptr  |-> vis1_pre)
  **  ((( &( "fin" ) )) # Ptr  |-> fin_pre)
  **  ((( &( "timer_p" ) )) # Ptr  |-> timer_p_pre)
  **  (SllPtrArray.full radj_pre n_pre radj_rows_low_level_spec )
  **  (IntArray.full fin_pre n_pre fin_m )
  **  (IntArray.full timer_p_pre 1 (cons (timer_m) ((@nil Z))) )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition kosaraju_finish_entail_wit_1 := 
(
forall (timer_p_pre: Z) (fin_pre: Z) (vis1_pre: Z) (radj_pre: Z) (n_pre: Z) (radj_rows_low_level_spec: (@list (@list Z))) (X_low_level_spec: (unit -> (KSt -> Prop))) (scc_next_v_abs_low_level_spec: Z) (timer_v_low_level_spec: Z) (sid_l_abs_low_level_spec: (@list Z)) (fin_l_low_level_spec: (@list Z)) (vis2_l_abs_low_level_spec: (@list Z)) (vis1_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (PreH1 : (safeExec (pre_kosaraju (g_low_level_spec) (vis1_l_low_level_spec) (vis2_l_abs_low_level_spec) (fin_l_low_level_spec) (sid_l_abs_low_level_spec) (timer_v_low_level_spec) (scc_next_v_abs_low_level_spec)) kosaraju_finish_monad X_low_level_spec )) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= INT_MAX)) ,
  (SllPtrArray.full radj_pre n_pre radj_rows_low_level_spec )
  **  (IntArray.full vis1_pre n_pre vis1_l_low_level_spec )
  **  (IntArray.full fin_pre n_pre fin_l_low_level_spec )
  **  (IntArray.full timer_p_pre 1 (cons (timer_v_low_level_spec) ((@nil Z))) )
|--
  EX (vis1_m: (@list Z))  (fin_m: (@list Z))  (timer_m: Z) ,
  “ (safeExec (pre_kosaraju (g_low_level_spec) (vis1_m) (vis2_l_abs_low_level_spec) (fin_m) (sid_l_abs_low_level_spec) (timer_m) (scc_next_v_abs_low_level_spec)) (kosaraju_finish_from (0)) X_low_level_spec ) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ”
  &&  (SllPtrArray.full radj_pre n_pre radj_rows_low_level_spec )
  **  (IntArray.full vis1_pre n_pre vis1_m )
  **  (IntArray.full fin_pre n_pre fin_m )
  **  (IntArray.full timer_p_pre 1 (cons (timer_m) ((@nil Z))) )
) \/
(
forall (n_pre: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (scc_next_v_abs_low_level_spec: Z) (timer_v_low_level_spec: Z) (sid_l_abs_low_level_spec: (@list Z)) (fin_l_low_level_spec: (@list Z)) (vis2_l_abs_low_level_spec: (@list Z)) (vis1_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (PreH1 : (safeExec (pre_kosaraju (g_low_level_spec) (vis1_l_low_level_spec) (vis2_l_abs_low_level_spec) (fin_l_low_level_spec) (sid_l_abs_low_level_spec) (timer_v_low_level_spec) (scc_next_v_abs_low_level_spec)) kosaraju_finish_monad X_low_level_spec )) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= INT_MAX)) ,
  TT && emp 
|--
  EX (timer_m: Z) ,
  “ ((cons (timer_v_low_level_spec) ((@nil Z))) = (cons (timer_m) ((@nil Z)))) ” 
  &&  “ (safeExec (pre_kosaraju (g_low_level_spec) (vis1_l_low_level_spec) (vis2_l_abs_low_level_spec) (fin_l_low_level_spec) (sid_l_abs_low_level_spec) (timer_m) (scc_next_v_abs_low_level_spec)) (kosaraju_finish_from (0)) X_low_level_spec ) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ”
  &&  emp
).

Definition kosaraju_finish_entail_wit_2 := 
(
forall (timer_p_pre: Z) (fin_pre: Z) (vis1_pre: Z) (radj_pre: Z) (n_pre: Z) (radj_rows_low_level_spec: (@list (@list Z))) (X_low_level_spec: (unit -> (KSt -> Prop))) (scc_next_v_abs_low_level_spec: Z) (sid_l_abs_low_level_spec: (@list Z)) (vis2_l_abs_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (i: Z) (vis1_m: (@list Z)) (fin_m: (@list Z)) (timer_m: Z) (PreH1 : ((Znth i vis1_m 0) = 0)) (PreH2 : (i < n_pre)) (PreH3 : (safeExec (pre_kosaraju (g_low_level_spec) (vis1_m) (vis2_l_abs_low_level_spec) (fin_m) (sid_l_abs_low_level_spec) (timer_m) (scc_next_v_abs_low_level_spec)) (kosaraju_finish_from (i)) X_low_level_spec )) (PreH4 : (0 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (n_pre <= INT_MAX)) ,
  (IntArray.full vis1_pre n_pre vis1_m )
  **  (SllPtrArray.full radj_pre n_pre radj_rows_low_level_spec )
  **  (IntArray.full fin_pre n_pre fin_m )
  **  (IntArray.full timer_p_pre 1 (cons (timer_m) ((@nil Z))) )
|--
  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ ((Znth (i) (vis1_m) (0)) = 0) ” 
  &&  “ (safeExec (pre_dfs1 (g_low_level_spec) (vis1_m) (fin_m) (timer_m)) (dfs_finish (i)) X_low_level_spec ) ”
  &&  (SllPtrArray.full radj_pre n_pre radj_rows_low_level_spec )
  **  (IntArray.full vis1_pre n_pre vis1_m )
  **  (IntArray.full fin_pre n_pre fin_m )
  **  (IntArray.full timer_p_pre 1 (cons (timer_m) ((@nil Z))) )
) \/
(
forall (n_pre: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (scc_next_v_abs_low_level_spec: Z) (sid_l_abs_low_level_spec: (@list Z)) (vis2_l_abs_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (i: Z) (vis1_m: (@list Z)) (fin_m: (@list Z)) (timer_m: Z) (PreH1 : ((Znth i vis1_m 0) = 0)) (PreH2 : (i < n_pre)) (PreH3 : (safeExec (pre_kosaraju (g_low_level_spec) (vis1_m) (vis2_l_abs_low_level_spec) (fin_m) (sid_l_abs_low_level_spec) (timer_m) (scc_next_v_abs_low_level_spec)) (kosaraju_finish_from (i)) X_low_level_spec )) (PreH4 : (0 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (n_pre <= INT_MAX)) ,
  TT && emp 
|--
  “ (safeExec (pre_dfs1 (g_low_level_spec) (vis1_m) (fin_m) (timer_m)) (dfs_finish (i)) X_low_level_spec ) ” 
  &&  “ ((Znth (i) (vis1_m) (0)) = 0) ”
  &&  emp
).

Definition kosaraju_finish_entail_wit_2_split_goal_1 := 
forall (n_pre: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (scc_next_v_abs_low_level_spec: Z) (sid_l_abs_low_level_spec: (@list Z)) (vis2_l_abs_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (i: Z) (vis1_m: (@list Z)) (fin_m: (@list Z)) (timer_m: Z) (PreH1 : ((Znth i vis1_m 0) = 0)) (PreH2 : (i < n_pre)) (PreH3 : (safeExec (pre_kosaraju (g_low_level_spec) (vis1_m) (vis2_l_abs_low_level_spec) (fin_m) (sid_l_abs_low_level_spec) (timer_m) (scc_next_v_abs_low_level_spec)) (kosaraju_finish_from (i)) X_low_level_spec )) (PreH4 : (0 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (n_pre <= INT_MAX)) ,
  TT && emp 
|--
  “ (safeExec (pre_dfs1 (g_low_level_spec) (vis1_m) (fin_m) (timer_m)) (dfs_finish (i)) X_low_level_spec ) ”
.

Definition kosaraju_finish_entail_wit_2_split_goal_2 := 
forall (n_pre: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (scc_next_v_abs_low_level_spec: Z) (sid_l_abs_low_level_spec: (@list Z)) (vis2_l_abs_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (i: Z) (vis1_m: (@list Z)) (fin_m: (@list Z)) (timer_m: Z) (PreH1 : ((Znth i vis1_m 0) = 0)) (PreH2 : (i < n_pre)) (PreH3 : (safeExec (pre_kosaraju (g_low_level_spec) (vis1_m) (vis2_l_abs_low_level_spec) (fin_m) (sid_l_abs_low_level_spec) (timer_m) (scc_next_v_abs_low_level_spec)) (kosaraju_finish_from (i)) X_low_level_spec )) (PreH4 : (0 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (n_pre <= INT_MAX)) ,
  TT && emp 
|--
  “ ((Znth (i) (vis1_m) (0)) = 0) ”
.

Definition kosaraju_finish_entail_wit_3_1 := 
(
forall (timer_p_pre: Z) (fin_pre: Z) (vis1_pre: Z) (radj_pre: Z) (n_pre: Z) (radj_rows_low_level_spec: (@list (@list Z))) (X_low_level_spec: (unit -> (KSt -> Prop))) (scc_next_v_abs_low_level_spec: Z) (sid_l_abs_low_level_spec: (@list Z)) (vis2_l_abs_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (vis1_m_2: (@list Z)) (i: Z) (vis1_l_: (@list Z)) (fin_l_: (@list Z)) (timer_v_: Z) (PreH1 : (safeExec (pre_dfs1 (g_low_level_spec) (vis1_l_) (fin_l_) (timer_v_)) (return (tt)) X_low_level_spec )) (PreH2 : (0 <= i)) (PreH3 : (i < n_pre)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : ((Znth (i) (vis1_m_2) (0)) = 0)) ,
  (SllPtrArray.full radj_pre n_pre radj_rows_low_level_spec )
  **  (IntArray.full vis1_pre n_pre vis1_l_ )
  **  (IntArray.full fin_pre n_pre fin_l_ )
  **  (IntArray.full timer_p_pre 1 (cons (timer_v_) ((@nil Z))) )
|--
  EX (vis1_m: (@list Z))  (fin_m: (@list Z))  (timer_m: Z) ,
  “ (safeExec (pre_kosaraju (g_low_level_spec) (vis1_m) (vis2_l_abs_low_level_spec) (fin_m) (sid_l_abs_low_level_spec) (timer_m) (scc_next_v_abs_low_level_spec)) (kosaraju_finish_from ((i + 1 ))) X_low_level_spec ) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ”
  &&  (SllPtrArray.full radj_pre n_pre radj_rows_low_level_spec )
  **  (IntArray.full vis1_pre n_pre vis1_m )
  **  (IntArray.full fin_pre n_pre fin_m )
  **  (IntArray.full timer_p_pre 1 (cons (timer_m) ((@nil Z))) )
) \/
(
forall (n_pre: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (scc_next_v_abs_low_level_spec: Z) (sid_l_abs_low_level_spec: (@list Z)) (vis2_l_abs_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (vis1_m_2: (@list Z)) (i: Z) (vis1_l_: (@list Z)) (fin_l_: (@list Z)) (timer_v_: Z) (PreH1 : (safeExec (pre_dfs1 (g_low_level_spec) (vis1_l_) (fin_l_) (timer_v_)) (return (tt)) X_low_level_spec )) (PreH2 : (0 <= i)) (PreH3 : (i < n_pre)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : ((Znth (i) (vis1_m_2) (0)) = 0)) ,
  TT && emp 
|--
  EX (timer_m: Z) ,
  “ ((cons (timer_v_) ((@nil Z))) = (cons (timer_m) ((@nil Z)))) ” 
  &&  “ (safeExec (pre_kosaraju (g_low_level_spec) (vis1_l_) (vis2_l_abs_low_level_spec) (fin_l_) (sid_l_abs_low_level_spec) (timer_m) (scc_next_v_abs_low_level_spec)) (kosaraju_finish_from ((i + 1 ))) X_low_level_spec ) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ”
  &&  emp
).

Definition kosaraju_finish_entail_wit_3_2 := 
(
forall (timer_p_pre: Z) (fin_pre: Z) (vis1_pre: Z) (radj_pre: Z) (n_pre: Z) (radj_rows_low_level_spec: (@list (@list Z))) (X_low_level_spec: (unit -> (KSt -> Prop))) (scc_next_v_abs_low_level_spec: Z) (sid_l_abs_low_level_spec: (@list Z)) (vis2_l_abs_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (vis1_m_2: (@list Z)) (fin_m_2: (@list Z)) (timer_m_2: Z) (i: Z) (PreH1 : ((Znth i vis1_m_2 0) <> 0)) (PreH2 : (i < n_pre)) (PreH3 : (safeExec (pre_kosaraju (g_low_level_spec) (vis1_m_2) (vis2_l_abs_low_level_spec) (fin_m_2) (sid_l_abs_low_level_spec) (timer_m_2) (scc_next_v_abs_low_level_spec)) (kosaraju_finish_from (i)) X_low_level_spec )) (PreH4 : (0 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (n_pre <= INT_MAX)) ,
  (IntArray.full vis1_pre n_pre vis1_m_2 )
  **  (SllPtrArray.full radj_pre n_pre radj_rows_low_level_spec )
  **  (IntArray.full fin_pre n_pre fin_m_2 )
  **  (IntArray.full timer_p_pre 1 (cons (timer_m_2) ((@nil Z))) )
|--
  EX (vis1_m: (@list Z))  (fin_m: (@list Z))  (timer_m: Z) ,
  “ (safeExec (pre_kosaraju (g_low_level_spec) (vis1_m) (vis2_l_abs_low_level_spec) (fin_m) (sid_l_abs_low_level_spec) (timer_m) (scc_next_v_abs_low_level_spec)) (kosaraju_finish_from ((i + 1 ))) X_low_level_spec ) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ”
  &&  (SllPtrArray.full radj_pre n_pre radj_rows_low_level_spec )
  **  (IntArray.full vis1_pre n_pre vis1_m )
  **  (IntArray.full fin_pre n_pre fin_m )
  **  (IntArray.full timer_p_pre 1 (cons (timer_m) ((@nil Z))) )
) \/
(
forall (n_pre: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (scc_next_v_abs_low_level_spec: Z) (sid_l_abs_low_level_spec: (@list Z)) (vis2_l_abs_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (vis1_m_2: (@list Z)) (fin_m_2: (@list Z)) (timer_m_2: Z) (i: Z) (PreH1 : ((Znth i vis1_m_2 0) <> 0)) (PreH2 : (i < n_pre)) (PreH3 : (safeExec (pre_kosaraju (g_low_level_spec) (vis1_m_2) (vis2_l_abs_low_level_spec) (fin_m_2) (sid_l_abs_low_level_spec) (timer_m_2) (scc_next_v_abs_low_level_spec)) (kosaraju_finish_from (i)) X_low_level_spec )) (PreH4 : (0 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (n_pre <= INT_MAX)) ,
  TT && emp 
|--
  EX (timer_m: Z) ,
  “ ((cons (timer_m_2) ((@nil Z))) = (cons (timer_m) ((@nil Z)))) ” 
  &&  “ (safeExec (pre_kosaraju (g_low_level_spec) (vis1_m_2) (vis2_l_abs_low_level_spec) (fin_m_2) (sid_l_abs_low_level_spec) (timer_m) (scc_next_v_abs_low_level_spec)) (kosaraju_finish_from ((i + 1 ))) X_low_level_spec ) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ”
  &&  emp
).

Definition kosaraju_finish_return_wit_1 := 
(
forall (timer_p_pre: Z) (fin_pre: Z) (vis1_pre: Z) (radj_pre: Z) (n_pre: Z) (radj_rows_low_level_spec: (@list (@list Z))) (X_low_level_spec: (unit -> (KSt -> Prop))) (scc_next_v_abs_low_level_spec: Z) (sid_l_abs_low_level_spec: (@list Z)) (vis2_l_abs_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (vis1_m: (@list Z)) (fin_m: (@list Z)) (timer_m: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (safeExec (pre_kosaraju (g_low_level_spec) (vis1_m) (vis2_l_abs_low_level_spec) (fin_m) (sid_l_abs_low_level_spec) (timer_m) (scc_next_v_abs_low_level_spec)) (kosaraju_finish_from (i)) X_low_level_spec )) (PreH3 : (0 <= i)) (PreH4 : (i <= n_pre)) (PreH5 : (n_pre <= INT_MAX)) ,
  (SllPtrArray.full radj_pre n_pre radj_rows_low_level_spec )
  **  (IntArray.full vis1_pre n_pre vis1_m )
  **  (IntArray.full fin_pre n_pre fin_m )
  **  (IntArray.full timer_p_pre 1 (cons (timer_m) ((@nil Z))) )
|--
  EX (vis1_l_: (@list Z))  (fin_l_: (@list Z))  (timer_v_: Z) ,
  “ (safeExec (pre_kosaraju (g_low_level_spec) (vis1_l_) (vis2_l_abs_low_level_spec) (fin_l_) (sid_l_abs_low_level_spec) (timer_v_) (scc_next_v_abs_low_level_spec)) (return (tt)) X_low_level_spec ) ”
  &&  (SllPtrArray.full radj_pre n_pre radj_rows_low_level_spec )
  **  (IntArray.full vis1_pre n_pre vis1_l_ )
  **  (IntArray.full fin_pre n_pre fin_l_ )
  **  (IntArray.full timer_p_pre 1 (cons (timer_v_) ((@nil Z))) )
) \/
(
forall (n_pre: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (scc_next_v_abs_low_level_spec: Z) (sid_l_abs_low_level_spec: (@list Z)) (vis2_l_abs_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (vis1_m: (@list Z)) (fin_m: (@list Z)) (timer_m: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (safeExec (pre_kosaraju (g_low_level_spec) (vis1_m) (vis2_l_abs_low_level_spec) (fin_m) (sid_l_abs_low_level_spec) (timer_m) (scc_next_v_abs_low_level_spec)) (kosaraju_finish_from (i)) X_low_level_spec )) (PreH3 : (0 <= i)) (PreH4 : (i <= n_pre)) (PreH5 : (n_pre <= INT_MAX)) ,
  TT && emp 
|--
  EX (timer_v_: Z) ,
  “ ((cons (timer_m) ((@nil Z))) = (cons (timer_v_) ((@nil Z)))) ” 
  &&  “ (safeExec (pre_kosaraju (g_low_level_spec) (vis1_m) (vis2_l_abs_low_level_spec) (fin_m) (sid_l_abs_low_level_spec) (timer_v_) (scc_next_v_abs_low_level_spec)) (return (tt)) X_low_level_spec ) ”
  &&  emp
).

Definition kosaraju_finish_partial_solve_wit_1 := 
forall (timer_p_pre: Z) (fin_pre: Z) (vis1_pre: Z) (radj_pre: Z) (n_pre: Z) (radj_rows_low_level_spec: (@list (@list Z))) (X_low_level_spec: (unit -> (KSt -> Prop))) (scc_next_v_abs_low_level_spec: Z) (sid_l_abs_low_level_spec: (@list Z)) (vis2_l_abs_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (vis1_m: (@list Z)) (fin_m: (@list Z)) (timer_m: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (safeExec (pre_kosaraju (g_low_level_spec) (vis1_m) (vis2_l_abs_low_level_spec) (fin_m) (sid_l_abs_low_level_spec) (timer_m) (scc_next_v_abs_low_level_spec)) (kosaraju_finish_from (i)) X_low_level_spec )) (PreH3 : (0 <= i)) (PreH4 : (i <= n_pre)) (PreH5 : (n_pre <= INT_MAX)) ,
  (SllPtrArray.full radj_pre n_pre radj_rows_low_level_spec )
  **  (IntArray.full vis1_pre n_pre vis1_m )
  **  (IntArray.full fin_pre n_pre fin_m )
  **  (IntArray.full timer_p_pre 1 (cons (timer_m) ((@nil Z))) )
|--
  “ (i < n_pre) ” 
  &&  “ (safeExec (pre_kosaraju (g_low_level_spec) (vis1_m) (vis2_l_abs_low_level_spec) (fin_m) (sid_l_abs_low_level_spec) (timer_m) (scc_next_v_abs_low_level_spec)) (kosaraju_finish_from (i)) X_low_level_spec ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ”
  &&  (((vis1_pre + (i * sizeof(INT) ) )) # Int  |-> (Znth i vis1_m 0))
  **  (IntArray.missing_i vis1_pre i 0 n_pre vis1_m )
  **  (SllPtrArray.full radj_pre n_pre radj_rows_low_level_spec )
  **  (IntArray.full fin_pre n_pre fin_m )
  **  (IntArray.full timer_p_pre 1 (cons (timer_m) ((@nil Z))) )
.

Definition kosaraju_finish_partial_solve_wit_2_pure := 
forall (timer_p_pre: Z) (fin_pre: Z) (vis1_pre: Z) (radj_pre: Z) (n_pre: Z) (radj_rows_low_level_spec: (@list (@list Z))) (X_low_level_spec: (unit -> (KSt -> Prop))) (g_low_level_spec: AdjGraph) (vis1_m: (@list Z)) (fin_m: (@list Z)) (timer_m: Z) (i: Z) (PreH1 : (0 <= i)) (PreH2 : (i < n_pre)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : ((Znth (i) (vis1_m) (0)) = 0)) (PreH5 : (safeExec (pre_dfs1 (g_low_level_spec) (vis1_m) (fin_m) (timer_m)) (dfs_finish (i)) X_low_level_spec )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "radj" ) )) # Ptr  |-> radj_pre)
  **  ((( &( "vis1" ) )) # Ptr  |-> vis1_pre)
  **  ((( &( "fin" ) )) # Ptr  |-> fin_pre)
  **  ((( &( "timer_p" ) )) # Ptr  |-> timer_p_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (SllPtrArray.full radj_pre n_pre radj_rows_low_level_spec )
  **  (IntArray.full vis1_pre n_pre vis1_m )
  **  (IntArray.full fin_pre n_pre fin_m )
  **  (IntArray.full timer_p_pre 1 (cons (timer_m) ((@nil Z))) )
|--
  “ (safeExec (pre_dfs1 (g_low_level_spec) (vis1_m) (fin_m) (timer_m)) (dfs_finish (i)) X_low_level_spec ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ”
.

Definition kosaraju_finish_partial_solve_wit_2_aux := 
forall (timer_p_pre: Z) (fin_pre: Z) (vis1_pre: Z) (radj_pre: Z) (n_pre: Z) (radj_rows_low_level_spec: (@list (@list Z))) (X_low_level_spec: (unit -> (KSt -> Prop))) (g_low_level_spec: AdjGraph) (vis1_m: (@list Z)) (fin_m: (@list Z)) (timer_m: Z) (i: Z) (PreH1 : (0 <= i)) (PreH2 : (i < n_pre)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : ((Znth (i) (vis1_m) (0)) = 0)) (PreH5 : (safeExec (pre_dfs1 (g_low_level_spec) (vis1_m) (fin_m) (timer_m)) (dfs_finish (i)) X_low_level_spec )) ,
  (SllPtrArray.full radj_pre n_pre radj_rows_low_level_spec )
  **  (IntArray.full vis1_pre n_pre vis1_m )
  **  (IntArray.full fin_pre n_pre fin_m )
  **  (IntArray.full timer_p_pre 1 (cons (timer_m) ((@nil Z))) )
|--
  “ (safeExec (pre_dfs1 (g_low_level_spec) (vis1_m) (fin_m) (timer_m)) (dfs_finish (i)) X_low_level_spec ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ ((Znth (i) (vis1_m) (0)) = 0) ” 
  &&  “ (safeExec (pre_dfs1 (g_low_level_spec) (vis1_m) (fin_m) (timer_m)) (dfs_finish (i)) X_low_level_spec ) ”
  &&  (SllPtrArray.full radj_pre n_pre radj_rows_low_level_spec )
  **  (IntArray.full vis1_pre n_pre vis1_m )
  **  (IntArray.full fin_pre n_pre fin_m )
  **  (IntArray.full timer_p_pre 1 (cons (timer_m) ((@nil Z))) )
.

Definition kosaraju_finish_partial_solve_wit_2 := kosaraju_finish_partial_solve_wit_2_pure -> kosaraju_finish_partial_solve_wit_2_aux.

(*----- Function kosaraju_scc -----*)

Definition kosaraju_scc_safety_wit_1 := 
forall (fin_pre: Z) (order_pre: Z) (scc_next_p_pre: Z) (sid_pre: Z) (vis2_pre: Z) (fadj_pre: Z) (n_pre: Z) (fadj_rows_low_level_spec: (@list (@list Z))) (X_low_level_spec: (unit -> (KSt -> Prop))) (fin_l_low_level_spec: (@list Z)) (order_l_low_level_spec: (@list Z)) (scc_next_v_low_level_spec: Z) (timer_v_abs_low_level_spec: Z) (sid_l_low_level_spec: (@list Z)) (vis2_l_low_level_spec: (@list Z)) (vis1_l_abs_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (PreH1 : (safeExec (pre_kosaraju (g_low_level_spec) (vis1_l_abs_low_level_spec) (vis2_l_low_level_spec) (fin_l_low_level_spec) (sid_l_low_level_spec) (timer_v_abs_low_level_spec) (scc_next_v_low_level_spec)) kosaraju_scc_monad X_low_level_spec )) (PreH2 : (order_sorted order_l_low_level_spec fin_l_low_level_spec )) (PreH3 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth (j) (order_l_low_level_spec) (0))) /\ ((Znth (j) (order_l_low_level_spec) (0)) < n_pre)))) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre <= INT_MAX)) ,
  ((( &( "k" ) )) # Int  |->_)
  **  ((( &( "fin" ) )) # Ptr  |-> fin_pre)
  **  ((( &( "order" ) )) # Ptr  |-> order_pre)
  **  ((( &( "scc_next_p" ) )) # Ptr  |-> scc_next_p_pre)
  **  ((( &( "sid" ) )) # Ptr  |-> sid_pre)
  **  ((( &( "vis2" ) )) # Ptr  |-> vis2_pre)
  **  ((( &( "fadj" ) )) # Ptr  |-> fadj_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (SllPtrArray.full fadj_pre n_pre fadj_rows_low_level_spec )
  **  (IntArray.full vis2_pre n_pre vis2_l_low_level_spec )
  **  (IntArray.full sid_pre n_pre sid_l_low_level_spec )
  **  (IntArray.full scc_next_p_pre 1 (cons (scc_next_v_low_level_spec) ((@nil Z))) )
  **  (IntArray.full order_pre n_pre order_l_low_level_spec )
  **  (IntArray.full fin_pre n_pre fin_l_low_level_spec )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition kosaraju_scc_safety_wit_2 := 
forall (fin_pre: Z) (order_pre: Z) (scc_next_p_pre: Z) (sid_pre: Z) (vis2_pre: Z) (fadj_pre: Z) (n_pre: Z) (fadj_rows_low_level_spec: (@list (@list Z))) (X_low_level_spec: (unit -> (KSt -> Prop))) (fin_l_low_level_spec: (@list Z)) (order_l_low_level_spec: (@list Z)) (timer_v_abs_low_level_spec: Z) (vis1_l_abs_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (vis2_m: (@list Z)) (sid_m: (@list Z)) (scc_next_m: Z) (k: Z) (u: Z) (PreH1 : (0 <= k)) (PreH2 : (k < n_pre)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (u = (Znth (k) (order_l_low_level_spec) (0)))) (PreH5 : (0 <= u)) (PreH6 : (u < n_pre)) (PreH7 : (n_pre <= INT_MAX)) (PreH8 : (safeExec (pre_kosaraju (g_low_level_spec) (vis1_l_abs_low_level_spec) (vis2_m) (fin_l_low_level_spec) (sid_m) (timer_v_abs_low_level_spec) (scc_next_m)) (kosaraju_scc_from (k)) X_low_level_spec )) ,
  (IntArray.full vis2_pre n_pre vis2_m )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "fadj" ) )) # Ptr  |-> fadj_pre)
  **  ((( &( "vis2" ) )) # Ptr  |-> vis2_pre)
  **  ((( &( "sid" ) )) # Ptr  |-> sid_pre)
  **  ((( &( "scc_next_p" ) )) # Ptr  |-> scc_next_p_pre)
  **  ((( &( "order" ) )) # Ptr  |-> order_pre)
  **  ((( &( "fin" ) )) # Ptr  |-> fin_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "u" ) )) # Int  |-> u)
  **  (SllPtrArray.full fadj_pre n_pre fadj_rows_low_level_spec )
  **  (IntArray.full sid_pre n_pre sid_m )
  **  (IntArray.full scc_next_p_pre 1 (cons (scc_next_m) ((@nil Z))) )
  **  (IntArray.full order_pre n_pre order_l_low_level_spec )
  **  (IntArray.full fin_pre n_pre fin_l_low_level_spec )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition kosaraju_scc_safety_wit_3 := 
forall (fin_pre: Z) (order_pre: Z) (scc_next_p_pre: Z) (sid_pre: Z) (vis2_pre: Z) (fadj_pre: Z) (n_pre: Z) (fadj_rows_low_level_spec: (@list (@list Z))) (X_low_level_spec: (unit -> (KSt -> Prop))) (fin_l_low_level_spec: (@list Z)) (order_l_low_level_spec: (@list Z)) (timer_v_abs_low_level_spec: Z) (vis1_l_abs_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (vis2_m: (@list Z)) (sid_m: (@list Z)) (scc_next_m: Z) (k: Z) (u: Z) (PreH1 : (0 <= k)) (PreH2 : (k < n_pre)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (0 <= u)) (PreH5 : (u < n_pre)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : ((Znth (u) (vis2_m) (0)) = 0)) (PreH8 : (safeExec (pre_kosaraju (g_low_level_spec) (vis1_l_abs_low_level_spec) (vis2_m) (fin_l_low_level_spec) (sid_m) (timer_v_abs_low_level_spec) (scc_next_m)) (kosaraju_scc_from (k)) X_low_level_spec )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "fadj" ) )) # Ptr  |-> fadj_pre)
  **  ((( &( "vis2" ) )) # Ptr  |-> vis2_pre)
  **  ((( &( "sid" ) )) # Ptr  |-> sid_pre)
  **  ((( &( "scc_next_p" ) )) # Ptr  |-> scc_next_p_pre)
  **  ((( &( "order" ) )) # Ptr  |-> order_pre)
  **  ((( &( "fin" ) )) # Ptr  |-> fin_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "u" ) )) # Int  |-> u)
  **  (SllPtrArray.full fadj_pre n_pre fadj_rows_low_level_spec )
  **  (IntArray.full vis2_pre n_pre vis2_m )
  **  (IntArray.full sid_pre n_pre sid_m )
  **  (IntArray.full scc_next_p_pre 1 (cons (scc_next_m) ((@nil Z))) )
  **  (IntArray.full order_pre n_pre order_l_low_level_spec )
  **  (IntArray.full fin_pre n_pre fin_l_low_level_spec )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition kosaraju_scc_safety_wit_4 := 
forall (fin_pre: Z) (order_pre: Z) (scc_next_p_pre: Z) (sid_pre: Z) (vis2_pre: Z) (fadj_pre: Z) (n_pre: Z) (fadj_rows_low_level_spec: (@list (@list Z))) (X_low_level_spec: (unit -> (KSt -> Prop))) (fin_l_low_level_spec: (@list Z)) (order_l_low_level_spec: (@list Z)) (timer_v_abs_low_level_spec: Z) (vis1_l_abs_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (vis2_m: (@list Z)) (sid_m: (@list Z)) (scc_next_m: Z) (k: Z) (u: Z) (PreH1 : (0 <= k)) (PreH2 : (k < n_pre)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (0 <= u)) (PreH5 : (u < n_pre)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : ((Znth (u) (vis2_m) (0)) = 0)) (PreH8 : (safeExec (pre_kosaraju (g_low_level_spec) (vis1_l_abs_low_level_spec) (vis2_m) (fin_l_low_level_spec) (sid_m) (timer_v_abs_low_level_spec) (scc_next_m)) (kosaraju_scc_from (k)) X_low_level_spec )) ,
  (IntArray.full sid_pre n_pre (replace_Znth (u) ((Znth 0 (cons (scc_next_m) ((@nil Z))) 0)) (sid_m)) )
  **  (IntArray.full scc_next_p_pre 1 (cons (scc_next_m) ((@nil Z))) )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "fadj" ) )) # Ptr  |-> fadj_pre)
  **  ((( &( "vis2" ) )) # Ptr  |-> vis2_pre)
  **  ((( &( "sid" ) )) # Ptr  |-> sid_pre)
  **  ((( &( "scc_next_p" ) )) # Ptr  |-> scc_next_p_pre)
  **  ((( &( "order" ) )) # Ptr  |-> order_pre)
  **  ((( &( "fin" ) )) # Ptr  |-> fin_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "u" ) )) # Int  |-> u)
  **  (SllPtrArray.full fadj_pre n_pre fadj_rows_low_level_spec )
  **  (IntArray.full vis2_pre n_pre vis2_m )
  **  (IntArray.full order_pre n_pre order_l_low_level_spec )
  **  (IntArray.full fin_pre n_pre fin_l_low_level_spec )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition kosaraju_scc_safety_wit_5 := 
(
forall (fin_pre: Z) (order_pre: Z) (scc_next_p_pre: Z) (sid_pre: Z) (vis2_pre: Z) (fadj_pre: Z) (n_pre: Z) (fadj_rows_low_level_spec: (@list (@list Z))) (X_low_level_spec: (unit -> (KSt -> Prop))) (fin_l_low_level_spec: (@list Z)) (order_l_low_level_spec: (@list Z)) (timer_v_abs_low_level_spec: Z) (vis1_l_abs_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (vis2_m: (@list Z)) (sid_m: (@list Z)) (scc_next_m: Z) (k: Z) (u: Z) (PreH1 : (0 <= k)) (PreH2 : (k < n_pre)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (0 <= u)) (PreH5 : (u < n_pre)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : ((Znth (u) (vis2_m) (0)) = 0)) (PreH8 : (safeExec (pre_kosaraju (g_low_level_spec) (vis1_l_abs_low_level_spec) (vis2_m) (fin_l_low_level_spec) (sid_m) (timer_v_abs_low_level_spec) (scc_next_m)) (kosaraju_scc_from (k)) X_low_level_spec )) ,
  (IntArray.full scc_next_p_pre 1 (cons (scc_next_m) ((@nil Z))) )
  **  (IntArray.full sid_pre n_pre (replace_Znth (u) ((Znth 0 (cons (scc_next_m) ((@nil Z))) 0)) (sid_m)) )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "fadj" ) )) # Ptr  |-> fadj_pre)
  **  ((( &( "vis2" ) )) # Ptr  |-> vis2_pre)
  **  ((( &( "sid" ) )) # Ptr  |-> sid_pre)
  **  ((( &( "scc_next_p" ) )) # Ptr  |-> scc_next_p_pre)
  **  ((( &( "order" ) )) # Ptr  |-> order_pre)
  **  ((( &( "fin" ) )) # Ptr  |-> fin_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "u" ) )) # Int  |-> u)
  **  (SllPtrArray.full fadj_pre n_pre fadj_rows_low_level_spec )
  **  (IntArray.full vis2_pre n_pre vis2_m )
  **  (IntArray.full order_pre n_pre order_l_low_level_spec )
  **  (IntArray.full fin_pre n_pre fin_l_low_level_spec )
|--
  “ (((Znth 0 (cons (scc_next_m) ((@nil Z))) 0) + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth 0 (cons (scc_next_m) ((@nil Z))) 0) + 1 )) ”
) \/
(
forall (fin_pre: Z) (order_pre: Z) (scc_next_p_pre: Z) (sid_pre: Z) (vis2_pre: Z) (fadj_pre: Z) (n_pre: Z) (fadj_rows_low_level_spec: (@list (@list Z))) (X_low_level_spec: (unit -> (KSt -> Prop))) (fin_l_low_level_spec: (@list Z)) (order_l_low_level_spec: (@list Z)) (timer_v_abs_low_level_spec: Z) (vis1_l_abs_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (vis2_m: (@list Z)) (sid_m: (@list Z)) (scc_next_m: Z) (k: Z) (u: Z) (PreH1 : (0 <= k)) (PreH2 : (k < n_pre)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (0 <= u)) (PreH5 : (u < n_pre)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : ((Znth (u) (vis2_m) (0)) = 0)) (PreH8 : (safeExec (pre_kosaraju (g_low_level_spec) (vis1_l_abs_low_level_spec) (vis2_m) (fin_l_low_level_spec) (sid_m) (timer_v_abs_low_level_spec) (scc_next_m)) (kosaraju_scc_from (k)) X_low_level_spec )) ,
  (IntArray.full scc_next_p_pre 1 (cons (scc_next_m) ((@nil Z))) )
  **  (IntArray.full sid_pre n_pre (replace_Znth (u) ((Znth 0 (cons (scc_next_m) ((@nil Z))) 0)) (sid_m)) )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "fadj" ) )) # Ptr  |-> fadj_pre)
  **  ((( &( "vis2" ) )) # Ptr  |-> vis2_pre)
  **  ((( &( "sid" ) )) # Ptr  |-> sid_pre)
  **  ((( &( "scc_next_p" ) )) # Ptr  |-> scc_next_p_pre)
  **  ((( &( "order" ) )) # Ptr  |-> order_pre)
  **  ((( &( "fin" ) )) # Ptr  |-> fin_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "u" ) )) # Int  |-> u)
  **  (SllPtrArray.full fadj_pre n_pre fadj_rows_low_level_spec )
  **  (IntArray.full vis2_pre n_pre vis2_m )
  **  (IntArray.full order_pre n_pre order_l_low_level_spec )
  **  (IntArray.full fin_pre n_pre fin_l_low_level_spec )
|--
  “ (((Znth 0 (cons (scc_next_m) ((@nil Z))) 0) + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth 0 (cons (scc_next_m) ((@nil Z))) 0) + 1 )) ”
).

Definition kosaraju_scc_safety_wit_5_split_goal_1 := 
forall (fin_pre: Z) (order_pre: Z) (scc_next_p_pre: Z) (sid_pre: Z) (vis2_pre: Z) (fadj_pre: Z) (n_pre: Z) (fadj_rows_low_level_spec: (@list (@list Z))) (X_low_level_spec: (unit -> (KSt -> Prop))) (fin_l_low_level_spec: (@list Z)) (order_l_low_level_spec: (@list Z)) (timer_v_abs_low_level_spec: Z) (vis1_l_abs_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (vis2_m: (@list Z)) (sid_m: (@list Z)) (scc_next_m: Z) (k: Z) (u: Z) (PreH1 : (0 <= k)) (PreH2 : (k < n_pre)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (0 <= u)) (PreH5 : (u < n_pre)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : ((Znth (u) (vis2_m) (0)) = 0)) (PreH8 : (safeExec (pre_kosaraju (g_low_level_spec) (vis1_l_abs_low_level_spec) (vis2_m) (fin_l_low_level_spec) (sid_m) (timer_v_abs_low_level_spec) (scc_next_m)) (kosaraju_scc_from (k)) X_low_level_spec )) ,
  (IntArray.full scc_next_p_pre 1 (cons (scc_next_m) ((@nil Z))) )
  **  (IntArray.full sid_pre n_pre (replace_Znth (u) ((Znth 0 (cons (scc_next_m) ((@nil Z))) 0)) (sid_m)) )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "fadj" ) )) # Ptr  |-> fadj_pre)
  **  ((( &( "vis2" ) )) # Ptr  |-> vis2_pre)
  **  ((( &( "sid" ) )) # Ptr  |-> sid_pre)
  **  ((( &( "scc_next_p" ) )) # Ptr  |-> scc_next_p_pre)
  **  ((( &( "order" ) )) # Ptr  |-> order_pre)
  **  ((( &( "fin" ) )) # Ptr  |-> fin_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "u" ) )) # Int  |-> u)
  **  (SllPtrArray.full fadj_pre n_pre fadj_rows_low_level_spec )
  **  (IntArray.full vis2_pre n_pre vis2_m )
  **  (IntArray.full order_pre n_pre order_l_low_level_spec )
  **  (IntArray.full fin_pre n_pre fin_l_low_level_spec )
|--
  “ (((Znth 0 (cons (scc_next_m) ((@nil Z))) 0) + 1 ) <= INT_MAX) ”
.

Definition kosaraju_scc_safety_wit_5_split_goal_2 := 
forall (fin_pre: Z) (order_pre: Z) (scc_next_p_pre: Z) (sid_pre: Z) (vis2_pre: Z) (fadj_pre: Z) (n_pre: Z) (fadj_rows_low_level_spec: (@list (@list Z))) (X_low_level_spec: (unit -> (KSt -> Prop))) (fin_l_low_level_spec: (@list Z)) (order_l_low_level_spec: (@list Z)) (timer_v_abs_low_level_spec: Z) (vis1_l_abs_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (vis2_m: (@list Z)) (sid_m: (@list Z)) (scc_next_m: Z) (k: Z) (u: Z) (PreH1 : (0 <= k)) (PreH2 : (k < n_pre)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (0 <= u)) (PreH5 : (u < n_pre)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : ((Znth (u) (vis2_m) (0)) = 0)) (PreH8 : (safeExec (pre_kosaraju (g_low_level_spec) (vis1_l_abs_low_level_spec) (vis2_m) (fin_l_low_level_spec) (sid_m) (timer_v_abs_low_level_spec) (scc_next_m)) (kosaraju_scc_from (k)) X_low_level_spec )) ,
  (IntArray.full scc_next_p_pre 1 (cons (scc_next_m) ((@nil Z))) )
  **  (IntArray.full sid_pre n_pre (replace_Znth (u) ((Znth 0 (cons (scc_next_m) ((@nil Z))) 0)) (sid_m)) )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "fadj" ) )) # Ptr  |-> fadj_pre)
  **  ((( &( "vis2" ) )) # Ptr  |-> vis2_pre)
  **  ((( &( "sid" ) )) # Ptr  |-> sid_pre)
  **  ((( &( "scc_next_p" ) )) # Ptr  |-> scc_next_p_pre)
  **  ((( &( "order" ) )) # Ptr  |-> order_pre)
  **  ((( &( "fin" ) )) # Ptr  |-> fin_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "u" ) )) # Int  |-> u)
  **  (SllPtrArray.full fadj_pre n_pre fadj_rows_low_level_spec )
  **  (IntArray.full vis2_pre n_pre vis2_m )
  **  (IntArray.full order_pre n_pre order_l_low_level_spec )
  **  (IntArray.full fin_pre n_pre fin_l_low_level_spec )
|--
  “ ((INT_MIN) <= ((Znth 0 (cons (scc_next_m) ((@nil Z))) 0) + 1 )) ”
.

Definition kosaraju_scc_safety_wit_6 := 
forall (fin_pre: Z) (order_pre: Z) (scc_next_p_pre: Z) (sid_pre: Z) (vis2_pre: Z) (fadj_pre: Z) (n_pre: Z) (fadj_rows_low_level_spec: (@list (@list Z))) (X_low_level_spec: (unit -> (KSt -> Prop))) (fin_l_low_level_spec: (@list Z)) (order_l_low_level_spec: (@list Z)) (timer_v_abs_low_level_spec: Z) (vis1_l_abs_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (vis2_m: (@list Z)) (sid_m: (@list Z)) (scc_next_m: Z) (k: Z) (u: Z) (PreH1 : (0 <= k)) (PreH2 : (k < n_pre)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (0 <= u)) (PreH5 : (u < n_pre)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : ((Znth (u) (vis2_m) (0)) = 0)) (PreH8 : (safeExec (pre_kosaraju (g_low_level_spec) (vis1_l_abs_low_level_spec) (vis2_m) (fin_l_low_level_spec) (sid_m) (timer_v_abs_low_level_spec) (scc_next_m)) (kosaraju_scc_from (k)) X_low_level_spec )) ,
  (IntArray.full sid_pre n_pre (replace_Znth (u) ((Znth 0 (cons (scc_next_m) ((@nil Z))) 0)) (sid_m)) )
  **  (IntArray.full scc_next_p_pre 1 (cons (scc_next_m) ((@nil Z))) )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "fadj" ) )) # Ptr  |-> fadj_pre)
  **  ((( &( "vis2" ) )) # Ptr  |-> vis2_pre)
  **  ((( &( "sid" ) )) # Ptr  |-> sid_pre)
  **  ((( &( "scc_next_p" ) )) # Ptr  |-> scc_next_p_pre)
  **  ((( &( "order" ) )) # Ptr  |-> order_pre)
  **  ((( &( "fin" ) )) # Ptr  |-> fin_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "u" ) )) # Int  |-> u)
  **  (SllPtrArray.full fadj_pre n_pre fadj_rows_low_level_spec )
  **  (IntArray.full vis2_pre n_pre vis2_m )
  **  (IntArray.full order_pre n_pre order_l_low_level_spec )
  **  (IntArray.full fin_pre n_pre fin_l_low_level_spec )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition kosaraju_scc_safety_wit_7 := 
forall (fin_pre: Z) (order_pre: Z) (scc_next_p_pre: Z) (sid_pre: Z) (vis2_pre: Z) (fadj_pre: Z) (n_pre: Z) (fadj_rows_low_level_spec: (@list (@list Z))) (X_low_level_spec: (unit -> (KSt -> Prop))) (fin_l_low_level_spec: (@list Z)) (order_l_low_level_spec: (@list Z)) (timer_v_abs_low_level_spec: Z) (vis1_l_abs_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (vis2_m: (@list Z)) (sid_m: (@list Z)) (scc_next_m: Z) (k: Z) (u: Z) (PreH1 : (0 <= k)) (PreH2 : (k < n_pre)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (0 <= u)) (PreH5 : (u < n_pre)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : ((Znth (u) (vis2_m) (0)) = 0)) (PreH8 : (safeExec (pre_kosaraju (g_low_level_spec) (vis1_l_abs_low_level_spec) (vis2_m) (fin_l_low_level_spec) (sid_m) (timer_v_abs_low_level_spec) (scc_next_m)) (kosaraju_scc_from (k)) X_low_level_spec )) ,
  (IntArray.full scc_next_p_pre 1 (cons (scc_next_m) ((@nil Z))) )
  **  (IntArray.full sid_pre n_pre (replace_Znth (u) ((Znth 0 (cons (scc_next_m) ((@nil Z))) 0)) (sid_m)) )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "fadj" ) )) # Ptr  |-> fadj_pre)
  **  ((( &( "vis2" ) )) # Ptr  |-> vis2_pre)
  **  ((( &( "sid" ) )) # Ptr  |-> sid_pre)
  **  ((( &( "scc_next_p" ) )) # Ptr  |-> scc_next_p_pre)
  **  ((( &( "order" ) )) # Ptr  |-> order_pre)
  **  ((( &( "fin" ) )) # Ptr  |-> fin_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "u" ) )) # Int  |-> u)
  **  (SllPtrArray.full fadj_pre n_pre fadj_rows_low_level_spec )
  **  (IntArray.full vis2_pre n_pre vis2_m )
  **  (IntArray.full order_pre n_pre order_l_low_level_spec )
  **  (IntArray.full fin_pre n_pre fin_l_low_level_spec )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition kosaraju_scc_safety_wit_8 := 
forall (fin_pre: Z) (order_pre: Z) (scc_next_p_pre: Z) (sid_pre: Z) (vis2_pre: Z) (fadj_pre: Z) (n_pre: Z) (fadj_rows_low_level_spec: (@list (@list Z))) (X_low_level_spec: (unit -> (KSt -> Prop))) (fin_l_low_level_spec: (@list Z)) (order_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (vis2_m: (@list Z)) (scc_next_m: Z) (k: Z) (u: Z) (vis2_l_: (@list Z)) (sid_l_: (@list Z)) (PreH1 : (safeExec (pre_dfs2 (g_low_level_spec) (vis2_l_) (sid_l_)) (return (tt)) X_low_level_spec )) (PreH2 : (0 <= k)) (PreH3 : (k < n_pre)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : (0 <= u)) (PreH6 : (u < n_pre)) (PreH7 : (n_pre <= INT_MAX)) (PreH8 : ((Znth (u) (vis2_m) (0)) = 0)) ,
  (SllPtrArray.full fadj_pre n_pre fadj_rows_low_level_spec )
  **  (IntArray.full vis2_pre n_pre vis2_l_ )
  **  (IntArray.full sid_pre n_pre sid_l_ )
  **  (IntArray.full scc_next_p_pre 1 (replace_Znth (0) (((Znth 0 (cons (scc_next_m) ((@nil Z))) 0) + 1 )) ((cons (scc_next_m) ((@nil Z))))) )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "fadj" ) )) # Ptr  |-> fadj_pre)
  **  ((( &( "vis2" ) )) # Ptr  |-> vis2_pre)
  **  ((( &( "sid" ) )) # Ptr  |-> sid_pre)
  **  ((( &( "scc_next_p" ) )) # Ptr  |-> scc_next_p_pre)
  **  ((( &( "order" ) )) # Ptr  |-> order_pre)
  **  ((( &( "fin" ) )) # Ptr  |-> fin_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  (IntArray.full order_pre n_pre order_l_low_level_spec )
  **  (IntArray.full fin_pre n_pre fin_l_low_level_spec )
|--
  “ ((k + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (k + 1 )) ”
.

Definition kosaraju_scc_safety_wit_9 := 
forall (fin_pre: Z) (order_pre: Z) (scc_next_p_pre: Z) (sid_pre: Z) (vis2_pre: Z) (fadj_pre: Z) (n_pre: Z) (fadj_rows_low_level_spec: (@list (@list Z))) (X_low_level_spec: (unit -> (KSt -> Prop))) (fin_l_low_level_spec: (@list Z)) (order_l_low_level_spec: (@list Z)) (timer_v_abs_low_level_spec: Z) (vis1_l_abs_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (vis2_m: (@list Z)) (sid_m: (@list Z)) (scc_next_m: Z) (k: Z) (u: Z) (PreH1 : ((Znth u vis2_m 0) <> 0)) (PreH2 : (0 <= k)) (PreH3 : (k < n_pre)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : (u = (Znth (k) (order_l_low_level_spec) (0)))) (PreH6 : (0 <= u)) (PreH7 : (u < n_pre)) (PreH8 : (n_pre <= INT_MAX)) (PreH9 : (safeExec (pre_kosaraju (g_low_level_spec) (vis1_l_abs_low_level_spec) (vis2_m) (fin_l_low_level_spec) (sid_m) (timer_v_abs_low_level_spec) (scc_next_m)) (kosaraju_scc_from (k)) X_low_level_spec )) ,
  (IntArray.full vis2_pre n_pre vis2_m )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "fadj" ) )) # Ptr  |-> fadj_pre)
  **  ((( &( "vis2" ) )) # Ptr  |-> vis2_pre)
  **  ((( &( "sid" ) )) # Ptr  |-> sid_pre)
  **  ((( &( "scc_next_p" ) )) # Ptr  |-> scc_next_p_pre)
  **  ((( &( "order" ) )) # Ptr  |-> order_pre)
  **  ((( &( "fin" ) )) # Ptr  |-> fin_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  (SllPtrArray.full fadj_pre n_pre fadj_rows_low_level_spec )
  **  (IntArray.full sid_pre n_pre sid_m )
  **  (IntArray.full scc_next_p_pre 1 (cons (scc_next_m) ((@nil Z))) )
  **  (IntArray.full order_pre n_pre order_l_low_level_spec )
  **  (IntArray.full fin_pre n_pre fin_l_low_level_spec )
|--
  “ ((k + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (k + 1 )) ”
.

Definition kosaraju_scc_entail_wit_1 := 
(
forall (fin_pre: Z) (order_pre: Z) (scc_next_p_pre: Z) (sid_pre: Z) (vis2_pre: Z) (fadj_pre: Z) (n_pre: Z) (fadj_rows_low_level_spec: (@list (@list Z))) (X_low_level_spec: (unit -> (KSt -> Prop))) (fin_l_low_level_spec: (@list Z)) (order_l_low_level_spec: (@list Z)) (scc_next_v_low_level_spec: Z) (timer_v_abs_low_level_spec: Z) (sid_l_low_level_spec: (@list Z)) (vis2_l_low_level_spec: (@list Z)) (vis1_l_abs_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (PreH1 : (safeExec (pre_kosaraju (g_low_level_spec) (vis1_l_abs_low_level_spec) (vis2_l_low_level_spec) (fin_l_low_level_spec) (sid_l_low_level_spec) (timer_v_abs_low_level_spec) (scc_next_v_low_level_spec)) kosaraju_scc_monad X_low_level_spec )) (PreH2 : (order_sorted order_l_low_level_spec fin_l_low_level_spec )) (PreH3 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < n_pre)) -> ((0 <= (Znth (j_2) (order_l_low_level_spec) (0))) /\ ((Znth (j_2) (order_l_low_level_spec) (0)) < n_pre)))) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre <= INT_MAX)) ,
  (SllPtrArray.full fadj_pre n_pre fadj_rows_low_level_spec )
  **  (IntArray.full vis2_pre n_pre vis2_l_low_level_spec )
  **  (IntArray.full sid_pre n_pre sid_l_low_level_spec )
  **  (IntArray.full scc_next_p_pre 1 (cons (scc_next_v_low_level_spec) ((@nil Z))) )
  **  (IntArray.full order_pre n_pre order_l_low_level_spec )
  **  (IntArray.full fin_pre n_pre fin_l_low_level_spec )
|--
  EX (vis2_m: (@list Z))  (sid_m: (@list Z))  (scc_next_m: Z) ,
  “ (safeExec (pre_kosaraju (g_low_level_spec) (vis1_l_abs_low_level_spec) (vis2_m) (fin_l_low_level_spec) (sid_m) (timer_v_abs_low_level_spec) (scc_next_m)) (kosaraju_scc_from (0)) X_low_level_spec ) ” 
  &&  “ (order_sorted order_l_low_level_spec fin_l_low_level_spec ) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth (j) (order_l_low_level_spec) (0))) /\ ((Znth (j) (order_l_low_level_spec) (0)) < n_pre))) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ”
  &&  (SllPtrArray.full fadj_pre n_pre fadj_rows_low_level_spec )
  **  (IntArray.full vis2_pre n_pre vis2_m )
  **  (IntArray.full sid_pre n_pre sid_m )
  **  (IntArray.full scc_next_p_pre 1 (cons (scc_next_m) ((@nil Z))) )
  **  (IntArray.full order_pre n_pre order_l_low_level_spec )
  **  (IntArray.full fin_pre n_pre fin_l_low_level_spec )
) \/
(
forall (n_pre: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (fin_l_low_level_spec: (@list Z)) (order_l_low_level_spec: (@list Z)) (scc_next_v_low_level_spec: Z) (timer_v_abs_low_level_spec: Z) (sid_l_low_level_spec: (@list Z)) (vis2_l_low_level_spec: (@list Z)) (vis1_l_abs_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (PreH1 : (safeExec (pre_kosaraju (g_low_level_spec) (vis1_l_abs_low_level_spec) (vis2_l_low_level_spec) (fin_l_low_level_spec) (sid_l_low_level_spec) (timer_v_abs_low_level_spec) (scc_next_v_low_level_spec)) kosaraju_scc_monad X_low_level_spec )) (PreH2 : (order_sorted order_l_low_level_spec fin_l_low_level_spec )) (PreH3 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < n_pre)) -> ((0 <= (Znth (j_2) (order_l_low_level_spec) (0))) /\ ((Znth (j_2) (order_l_low_level_spec) (0)) < n_pre)))) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre <= INT_MAX)) ,
  TT && emp 
|--
  EX (scc_next_m: Z) ,
  “ ((cons (scc_next_v_low_level_spec) ((@nil Z))) = (cons (scc_next_m) ((@nil Z)))) ” 
  &&  “ (safeExec (pre_kosaraju (g_low_level_spec) (vis1_l_abs_low_level_spec) (vis2_l_low_level_spec) (fin_l_low_level_spec) (sid_l_low_level_spec) (timer_v_abs_low_level_spec) (scc_next_m)) (kosaraju_scc_from (0)) X_low_level_spec ) ” 
  &&  “ (order_sorted order_l_low_level_spec fin_l_low_level_spec ) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth (j) (order_l_low_level_spec) (0))) /\ ((Znth (j) (order_l_low_level_spec) (0)) < n_pre))) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ”
  &&  emp
).

Definition kosaraju_scc_entail_wit_2 := 
(
forall (fin_pre: Z) (order_pre: Z) (scc_next_p_pre: Z) (sid_pre: Z) (vis2_pre: Z) (fadj_pre: Z) (n_pre: Z) (fadj_rows_low_level_spec: (@list (@list Z))) (X_low_level_spec: (unit -> (KSt -> Prop))) (fin_l_low_level_spec: (@list Z)) (order_l_low_level_spec: (@list Z)) (timer_v_abs_low_level_spec: Z) (vis1_l_abs_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (k: Z) (vis2_m: (@list Z)) (sid_m: (@list Z)) (scc_next_m: Z) (PreH1 : (k < n_pre)) (PreH2 : (safeExec (pre_kosaraju (g_low_level_spec) (vis1_l_abs_low_level_spec) (vis2_m) (fin_l_low_level_spec) (sid_m) (timer_v_abs_low_level_spec) (scc_next_m)) (kosaraju_scc_from (k)) X_low_level_spec )) (PreH3 : (order_sorted order_l_low_level_spec fin_l_low_level_spec )) (PreH4 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth (j) (order_l_low_level_spec) (0))) /\ ((Znth (j) (order_l_low_level_spec) (0)) < n_pre)))) (PreH5 : (0 <= k)) (PreH6 : (k <= n_pre)) (PreH7 : (n_pre <= INT_MAX)) ,
  (IntArray.full order_pre n_pre order_l_low_level_spec )
  **  (SllPtrArray.full fadj_pre n_pre fadj_rows_low_level_spec )
  **  (IntArray.full vis2_pre n_pre vis2_m )
  **  (IntArray.full sid_pre n_pre sid_m )
  **  (IntArray.full scc_next_p_pre 1 (cons (scc_next_m) ((@nil Z))) )
  **  (IntArray.full fin_pre n_pre fin_l_low_level_spec )
|--
  “ (0 <= k) ” 
  &&  “ (k < n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ ((Znth k order_l_low_level_spec 0) = (Znth (k) (order_l_low_level_spec) (0))) ” 
  &&  “ (0 <= (Znth k order_l_low_level_spec 0)) ” 
  &&  “ ((Znth k order_l_low_level_spec 0) < n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (safeExec (pre_kosaraju (g_low_level_spec) (vis1_l_abs_low_level_spec) (vis2_m) (fin_l_low_level_spec) (sid_m) (timer_v_abs_low_level_spec) (scc_next_m)) (kosaraju_scc_from (k)) X_low_level_spec ) ”
  &&  (SllPtrArray.full fadj_pre n_pre fadj_rows_low_level_spec )
  **  (IntArray.full vis2_pre n_pre vis2_m )
  **  (IntArray.full sid_pre n_pre sid_m )
  **  (IntArray.full scc_next_p_pre 1 (cons (scc_next_m) ((@nil Z))) )
  **  (IntArray.full order_pre n_pre order_l_low_level_spec )
  **  (IntArray.full fin_pre n_pre fin_l_low_level_spec )
) \/
(
forall (n_pre: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (fin_l_low_level_spec: (@list Z)) (order_l_low_level_spec: (@list Z)) (timer_v_abs_low_level_spec: Z) (vis1_l_abs_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (k: Z) (vis2_m: (@list Z)) (sid_m: (@list Z)) (scc_next_m: Z) (PreH1 : (k < n_pre)) (PreH2 : (safeExec (pre_kosaraju (g_low_level_spec) (vis1_l_abs_low_level_spec) (vis2_m) (fin_l_low_level_spec) (sid_m) (timer_v_abs_low_level_spec) (scc_next_m)) (kosaraju_scc_from (k)) X_low_level_spec )) (PreH3 : (order_sorted order_l_low_level_spec fin_l_low_level_spec )) (PreH4 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth (j) (order_l_low_level_spec) (0))) /\ ((Znth (j) (order_l_low_level_spec) (0)) < n_pre)))) (PreH5 : (0 <= k)) (PreH6 : (k <= n_pre)) (PreH7 : (n_pre <= INT_MAX)) ,
  TT && emp 
|--
  “ ((Znth k order_l_low_level_spec 0) < n_pre) ” 
  &&  “ (0 <= (Znth k order_l_low_level_spec 0)) ” 
  &&  “ ((Znth k order_l_low_level_spec 0) = (Znth (k) (order_l_low_level_spec) (0))) ”
  &&  emp
).

Definition kosaraju_scc_entail_wit_2_split_goal_1 := 
forall (n_pre: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (fin_l_low_level_spec: (@list Z)) (order_l_low_level_spec: (@list Z)) (timer_v_abs_low_level_spec: Z) (vis1_l_abs_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (k: Z) (vis2_m: (@list Z)) (sid_m: (@list Z)) (scc_next_m: Z) (PreH1 : (k < n_pre)) (PreH2 : (safeExec (pre_kosaraju (g_low_level_spec) (vis1_l_abs_low_level_spec) (vis2_m) (fin_l_low_level_spec) (sid_m) (timer_v_abs_low_level_spec) (scc_next_m)) (kosaraju_scc_from (k)) X_low_level_spec )) (PreH3 : (order_sorted order_l_low_level_spec fin_l_low_level_spec )) (PreH4 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth (j) (order_l_low_level_spec) (0))) /\ ((Znth (j) (order_l_low_level_spec) (0)) < n_pre)))) (PreH5 : (0 <= k)) (PreH6 : (k <= n_pre)) (PreH7 : (n_pre <= INT_MAX)) ,
  TT && emp 
|--
  “ ((Znth k order_l_low_level_spec 0) < n_pre) ”
.

Definition kosaraju_scc_entail_wit_2_split_goal_2 := 
forall (n_pre: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (fin_l_low_level_spec: (@list Z)) (order_l_low_level_spec: (@list Z)) (timer_v_abs_low_level_spec: Z) (vis1_l_abs_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (k: Z) (vis2_m: (@list Z)) (sid_m: (@list Z)) (scc_next_m: Z) (PreH1 : (k < n_pre)) (PreH2 : (safeExec (pre_kosaraju (g_low_level_spec) (vis1_l_abs_low_level_spec) (vis2_m) (fin_l_low_level_spec) (sid_m) (timer_v_abs_low_level_spec) (scc_next_m)) (kosaraju_scc_from (k)) X_low_level_spec )) (PreH3 : (order_sorted order_l_low_level_spec fin_l_low_level_spec )) (PreH4 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth (j) (order_l_low_level_spec) (0))) /\ ((Znth (j) (order_l_low_level_spec) (0)) < n_pre)))) (PreH5 : (0 <= k)) (PreH6 : (k <= n_pre)) (PreH7 : (n_pre <= INT_MAX)) ,
  TT && emp 
|--
  “ (0 <= (Znth k order_l_low_level_spec 0)) ”
.

Definition kosaraju_scc_entail_wit_2_split_goal_3 := 
forall (n_pre: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (fin_l_low_level_spec: (@list Z)) (order_l_low_level_spec: (@list Z)) (timer_v_abs_low_level_spec: Z) (vis1_l_abs_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (k: Z) (vis2_m: (@list Z)) (sid_m: (@list Z)) (scc_next_m: Z) (PreH1 : (k < n_pre)) (PreH2 : (safeExec (pre_kosaraju (g_low_level_spec) (vis1_l_abs_low_level_spec) (vis2_m) (fin_l_low_level_spec) (sid_m) (timer_v_abs_low_level_spec) (scc_next_m)) (kosaraju_scc_from (k)) X_low_level_spec )) (PreH3 : (order_sorted order_l_low_level_spec fin_l_low_level_spec )) (PreH4 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth (j) (order_l_low_level_spec) (0))) /\ ((Znth (j) (order_l_low_level_spec) (0)) < n_pre)))) (PreH5 : (0 <= k)) (PreH6 : (k <= n_pre)) (PreH7 : (n_pre <= INT_MAX)) ,
  TT && emp 
|--
  “ ((Znth k order_l_low_level_spec 0) = (Znth (k) (order_l_low_level_spec) (0))) ”
.

Definition kosaraju_scc_entail_wit_3 := 
(
forall (fin_pre: Z) (order_pre: Z) (scc_next_p_pre: Z) (sid_pre: Z) (vis2_pre: Z) (fadj_pre: Z) (n_pre: Z) (fadj_rows_low_level_spec: (@list (@list Z))) (X_low_level_spec: (unit -> (KSt -> Prop))) (fin_l_low_level_spec: (@list Z)) (order_l_low_level_spec: (@list Z)) (timer_v_abs_low_level_spec: Z) (vis1_l_abs_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (vis2_m: (@list Z)) (sid_m: (@list Z)) (scc_next_m: Z) (k: Z) (u: Z) (PreH1 : ((Znth u vis2_m 0) = 0)) (PreH2 : (0 <= k)) (PreH3 : (k < n_pre)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : (u = (Znth (k) (order_l_low_level_spec) (0)))) (PreH6 : (0 <= u)) (PreH7 : (u < n_pre)) (PreH8 : (n_pre <= INT_MAX)) (PreH9 : (safeExec (pre_kosaraju (g_low_level_spec) (vis1_l_abs_low_level_spec) (vis2_m) (fin_l_low_level_spec) (sid_m) (timer_v_abs_low_level_spec) (scc_next_m)) (kosaraju_scc_from (k)) X_low_level_spec )) ,
  (IntArray.full vis2_pre n_pre vis2_m )
  **  (SllPtrArray.full fadj_pre n_pre fadj_rows_low_level_spec )
  **  (IntArray.full sid_pre n_pre sid_m )
  **  (IntArray.full scc_next_p_pre 1 (cons (scc_next_m) ((@nil Z))) )
  **  (IntArray.full order_pre n_pre order_l_low_level_spec )
  **  (IntArray.full fin_pre n_pre fin_l_low_level_spec )
|--
  “ (0 <= k) ” 
  &&  “ (k < n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (0 <= u) ” 
  &&  “ (u < n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ ((Znth (u) (vis2_m) (0)) = 0) ” 
  &&  “ (safeExec (pre_kosaraju (g_low_level_spec) (vis1_l_abs_low_level_spec) (vis2_m) (fin_l_low_level_spec) (sid_m) (timer_v_abs_low_level_spec) (scc_next_m)) (kosaraju_scc_from (k)) X_low_level_spec ) ”
  &&  (SllPtrArray.full fadj_pre n_pre fadj_rows_low_level_spec )
  **  (IntArray.full vis2_pre n_pre vis2_m )
  **  (IntArray.full sid_pre n_pre sid_m )
  **  (IntArray.full scc_next_p_pre 1 (cons (scc_next_m) ((@nil Z))) )
  **  (IntArray.full order_pre n_pre order_l_low_level_spec )
  **  (IntArray.full fin_pre n_pre fin_l_low_level_spec )
) \/
(
forall (n_pre: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (fin_l_low_level_spec: (@list Z)) (order_l_low_level_spec: (@list Z)) (timer_v_abs_low_level_spec: Z) (vis1_l_abs_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (vis2_m: (@list Z)) (sid_m: (@list Z)) (scc_next_m: Z) (k: Z) (u: Z) (PreH1 : ((Znth u vis2_m 0) = 0)) (PreH2 : (0 <= k)) (PreH3 : (k < n_pre)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : (u = (Znth (k) (order_l_low_level_spec) (0)))) (PreH6 : (0 <= u)) (PreH7 : (u < n_pre)) (PreH8 : (n_pre <= INT_MAX)) (PreH9 : (safeExec (pre_kosaraju (g_low_level_spec) (vis1_l_abs_low_level_spec) (vis2_m) (fin_l_low_level_spec) (sid_m) (timer_v_abs_low_level_spec) (scc_next_m)) (kosaraju_scc_from (k)) X_low_level_spec )) ,
  TT && emp 
|--
  “ ((Znth (u) (vis2_m) (0)) = 0) ”
  &&  emp
).

Definition kosaraju_scc_entail_wit_3_split_goal_1 := 
forall (n_pre: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (fin_l_low_level_spec: (@list Z)) (order_l_low_level_spec: (@list Z)) (timer_v_abs_low_level_spec: Z) (vis1_l_abs_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (vis2_m: (@list Z)) (sid_m: (@list Z)) (scc_next_m: Z) (k: Z) (u: Z) (PreH1 : ((Znth u vis2_m 0) = 0)) (PreH2 : (0 <= k)) (PreH3 : (k < n_pre)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : (u = (Znth (k) (order_l_low_level_spec) (0)))) (PreH6 : (0 <= u)) (PreH7 : (u < n_pre)) (PreH8 : (n_pre <= INT_MAX)) (PreH9 : (safeExec (pre_kosaraju (g_low_level_spec) (vis1_l_abs_low_level_spec) (vis2_m) (fin_l_low_level_spec) (sid_m) (timer_v_abs_low_level_spec) (scc_next_m)) (kosaraju_scc_from (k)) X_low_level_spec )) ,
  TT && emp 
|--
  “ ((Znth (u) (vis2_m) (0)) = 0) ”
.

Definition kosaraju_scc_entail_wit_4_1 := 
(
forall (fin_pre: Z) (order_pre: Z) (scc_next_p_pre: Z) (sid_pre: Z) (vis2_pre: Z) (fadj_pre: Z) (n_pre: Z) (fadj_rows_low_level_spec: (@list (@list Z))) (X_low_level_spec: (unit -> (KSt -> Prop))) (fin_l_low_level_spec: (@list Z)) (order_l_low_level_spec: (@list Z)) (timer_v_abs_low_level_spec: Z) (vis1_l_abs_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (vis2_m_2: (@list Z)) (scc_next_m_2: Z) (k: Z) (u: Z) (vis2_l_: (@list Z)) (sid_l_: (@list Z)) (PreH1 : (safeExec (pre_dfs2 (g_low_level_spec) (vis2_l_) (sid_l_)) (return (tt)) X_low_level_spec )) (PreH2 : (0 <= k)) (PreH3 : (k < n_pre)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : (0 <= u)) (PreH6 : (u < n_pre)) (PreH7 : (n_pre <= INT_MAX)) (PreH8 : ((Znth (u) (vis2_m_2) (0)) = 0)) ,
  (SllPtrArray.full fadj_pre n_pre fadj_rows_low_level_spec )
  **  (IntArray.full vis2_pre n_pre vis2_l_ )
  **  (IntArray.full sid_pre n_pre sid_l_ )
  **  (IntArray.full scc_next_p_pre 1 (replace_Znth (0) (((Znth 0 (cons (scc_next_m_2) ((@nil Z))) 0) + 1 )) ((cons (scc_next_m_2) ((@nil Z))))) )
  **  (IntArray.full order_pre n_pre order_l_low_level_spec )
  **  (IntArray.full fin_pre n_pre fin_l_low_level_spec )
|--
  EX (vis2_m: (@list Z))  (sid_m: (@list Z))  (scc_next_m: Z) ,
  “ (safeExec (pre_kosaraju (g_low_level_spec) (vis1_l_abs_low_level_spec) (vis2_m) (fin_l_low_level_spec) (sid_m) (timer_v_abs_low_level_spec) (scc_next_m)) (kosaraju_scc_from ((k + 1 ))) X_low_level_spec ) ” 
  &&  “ (order_sorted order_l_low_level_spec fin_l_low_level_spec ) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth (j) (order_l_low_level_spec) (0))) /\ ((Znth (j) (order_l_low_level_spec) (0)) < n_pre))) ” 
  &&  “ (0 <= (k + 1 )) ” 
  &&  “ ((k + 1 ) <= n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ”
  &&  (SllPtrArray.full fadj_pre n_pre fadj_rows_low_level_spec )
  **  (IntArray.full vis2_pre n_pre vis2_m )
  **  (IntArray.full sid_pre n_pre sid_m )
  **  (IntArray.full scc_next_p_pre 1 (cons (scc_next_m) ((@nil Z))) )
  **  (IntArray.full order_pre n_pre order_l_low_level_spec )
  **  (IntArray.full fin_pre n_pre fin_l_low_level_spec )
) \/
(
forall (n_pre: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (fin_l_low_level_spec: (@list Z)) (order_l_low_level_spec: (@list Z)) (timer_v_abs_low_level_spec: Z) (vis1_l_abs_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (vis2_m_2: (@list Z)) (scc_next_m_2: Z) (k: Z) (u: Z) (vis2_l_: (@list Z)) (sid_l_: (@list Z)) (PreH1 : (safeExec (pre_dfs2 (g_low_level_spec) (vis2_l_) (sid_l_)) (return (tt)) X_low_level_spec )) (PreH2 : (0 <= k)) (PreH3 : (k < n_pre)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : (0 <= u)) (PreH6 : (u < n_pre)) (PreH7 : (n_pre <= INT_MAX)) (PreH8 : ((Znth (u) (vis2_m_2) (0)) = 0)) ,
  TT && emp 
|--
  EX (scc_next_m: Z) ,
  “ ((replace_Znth (0) (((Znth 0 (cons (scc_next_m_2) ((@nil Z))) 0) + 1 )) ((cons (scc_next_m_2) ((@nil Z))))) = (cons (scc_next_m) ((@nil Z)))) ” 
  &&  “ (safeExec (pre_kosaraju (g_low_level_spec) (vis1_l_abs_low_level_spec) (vis2_l_) (fin_l_low_level_spec) (sid_l_) (timer_v_abs_low_level_spec) (scc_next_m)) (kosaraju_scc_from ((k + 1 ))) X_low_level_spec ) ” 
  &&  “ (order_sorted order_l_low_level_spec fin_l_low_level_spec ) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth (j) (order_l_low_level_spec) (0))) /\ ((Znth (j) (order_l_low_level_spec) (0)) < n_pre))) ” 
  &&  “ (0 <= (k + 1 )) ” 
  &&  “ ((k + 1 ) <= n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ”
  &&  emp
).

Definition kosaraju_scc_entail_wit_4_2 := 
(
forall (fin_pre: Z) (order_pre: Z) (scc_next_p_pre: Z) (sid_pre: Z) (vis2_pre: Z) (fadj_pre: Z) (n_pre: Z) (fadj_rows_low_level_spec: (@list (@list Z))) (X_low_level_spec: (unit -> (KSt -> Prop))) (fin_l_low_level_spec: (@list Z)) (order_l_low_level_spec: (@list Z)) (timer_v_abs_low_level_spec: Z) (vis1_l_abs_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (vis2_m_2: (@list Z)) (sid_m_2: (@list Z)) (scc_next_m_2: Z) (k: Z) (u: Z) (PreH1 : ((Znth u vis2_m_2 0) <> 0)) (PreH2 : (0 <= k)) (PreH3 : (k < n_pre)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : (u = (Znth (k) (order_l_low_level_spec) (0)))) (PreH6 : (0 <= u)) (PreH7 : (u < n_pre)) (PreH8 : (n_pre <= INT_MAX)) (PreH9 : (safeExec (pre_kosaraju (g_low_level_spec) (vis1_l_abs_low_level_spec) (vis2_m_2) (fin_l_low_level_spec) (sid_m_2) (timer_v_abs_low_level_spec) (scc_next_m_2)) (kosaraju_scc_from (k)) X_low_level_spec )) ,
  (IntArray.full vis2_pre n_pre vis2_m_2 )
  **  (SllPtrArray.full fadj_pre n_pre fadj_rows_low_level_spec )
  **  (IntArray.full sid_pre n_pre sid_m_2 )
  **  (IntArray.full scc_next_p_pre 1 (cons (scc_next_m_2) ((@nil Z))) )
  **  (IntArray.full order_pre n_pre order_l_low_level_spec )
  **  (IntArray.full fin_pre n_pre fin_l_low_level_spec )
|--
  EX (vis2_m: (@list Z))  (sid_m: (@list Z))  (scc_next_m: Z) ,
  “ (safeExec (pre_kosaraju (g_low_level_spec) (vis1_l_abs_low_level_spec) (vis2_m) (fin_l_low_level_spec) (sid_m) (timer_v_abs_low_level_spec) (scc_next_m)) (kosaraju_scc_from ((k + 1 ))) X_low_level_spec ) ” 
  &&  “ (order_sorted order_l_low_level_spec fin_l_low_level_spec ) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth (j) (order_l_low_level_spec) (0))) /\ ((Znth (j) (order_l_low_level_spec) (0)) < n_pre))) ” 
  &&  “ (0 <= (k + 1 )) ” 
  &&  “ ((k + 1 ) <= n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ”
  &&  (SllPtrArray.full fadj_pre n_pre fadj_rows_low_level_spec )
  **  (IntArray.full vis2_pre n_pre vis2_m )
  **  (IntArray.full sid_pre n_pre sid_m )
  **  (IntArray.full scc_next_p_pre 1 (cons (scc_next_m) ((@nil Z))) )
  **  (IntArray.full order_pre n_pre order_l_low_level_spec )
  **  (IntArray.full fin_pre n_pre fin_l_low_level_spec )
) \/
(
forall (n_pre: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (fin_l_low_level_spec: (@list Z)) (order_l_low_level_spec: (@list Z)) (timer_v_abs_low_level_spec: Z) (vis1_l_abs_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (vis2_m_2: (@list Z)) (sid_m_2: (@list Z)) (scc_next_m_2: Z) (k: Z) (u: Z) (PreH1 : ((Znth u vis2_m_2 0) <> 0)) (PreH2 : (0 <= k)) (PreH3 : (k < n_pre)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : (u = (Znth (k) (order_l_low_level_spec) (0)))) (PreH6 : (0 <= u)) (PreH7 : (u < n_pre)) (PreH8 : (n_pre <= INT_MAX)) (PreH9 : (safeExec (pre_kosaraju (g_low_level_spec) (vis1_l_abs_low_level_spec) (vis2_m_2) (fin_l_low_level_spec) (sid_m_2) (timer_v_abs_low_level_spec) (scc_next_m_2)) (kosaraju_scc_from (k)) X_low_level_spec )) ,
  TT && emp 
|--
  EX (scc_next_m: Z) ,
  “ ((cons (scc_next_m_2) ((@nil Z))) = (cons (scc_next_m) ((@nil Z)))) ” 
  &&  “ (safeExec (pre_kosaraju (g_low_level_spec) (vis1_l_abs_low_level_spec) (vis2_m_2) (fin_l_low_level_spec) (sid_m_2) (timer_v_abs_low_level_spec) (scc_next_m)) (kosaraju_scc_from ((k + 1 ))) X_low_level_spec ) ” 
  &&  “ (order_sorted order_l_low_level_spec fin_l_low_level_spec ) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth (j) (order_l_low_level_spec) (0))) /\ ((Znth (j) (order_l_low_level_spec) (0)) < n_pre))) ” 
  &&  “ (0 <= (k + 1 )) ” 
  &&  “ ((k + 1 ) <= n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ”
  &&  emp
).

Definition kosaraju_scc_return_wit_1 := 
(
forall (fin_pre: Z) (order_pre: Z) (scc_next_p_pre: Z) (sid_pre: Z) (vis2_pre: Z) (fadj_pre: Z) (n_pre: Z) (fadj_rows_low_level_spec: (@list (@list Z))) (X_low_level_spec: (unit -> (KSt -> Prop))) (fin_l_low_level_spec: (@list Z)) (order_l_low_level_spec: (@list Z)) (timer_v_abs_low_level_spec: Z) (vis1_l_abs_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (vis2_m: (@list Z)) (sid_m: (@list Z)) (scc_next_m: Z) (k: Z) (PreH1 : (k >= n_pre)) (PreH2 : (safeExec (pre_kosaraju (g_low_level_spec) (vis1_l_abs_low_level_spec) (vis2_m) (fin_l_low_level_spec) (sid_m) (timer_v_abs_low_level_spec) (scc_next_m)) (kosaraju_scc_from (k)) X_low_level_spec )) (PreH3 : (order_sorted order_l_low_level_spec fin_l_low_level_spec )) (PreH4 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth (j) (order_l_low_level_spec) (0))) /\ ((Znth (j) (order_l_low_level_spec) (0)) < n_pre)))) (PreH5 : (0 <= k)) (PreH6 : (k <= n_pre)) (PreH7 : (n_pre <= INT_MAX)) ,
  (SllPtrArray.full fadj_pre n_pre fadj_rows_low_level_spec )
  **  (IntArray.full vis2_pre n_pre vis2_m )
  **  (IntArray.full sid_pre n_pre sid_m )
  **  (IntArray.full scc_next_p_pre 1 (cons (scc_next_m) ((@nil Z))) )
  **  (IntArray.full order_pre n_pre order_l_low_level_spec )
  **  (IntArray.full fin_pre n_pre fin_l_low_level_spec )
|--
  EX (vis2_l_: (@list Z))  (sid_l_: (@list Z))  (scc_next_v_: Z) ,
  “ (safeExec (pre_kosaraju (g_low_level_spec) (vis1_l_abs_low_level_spec) (vis2_l_) (fin_l_low_level_spec) (sid_l_) (timer_v_abs_low_level_spec) (scc_next_v_)) (return (tt)) X_low_level_spec ) ”
  &&  (SllPtrArray.full fadj_pre n_pre fadj_rows_low_level_spec )
  **  (IntArray.full vis2_pre n_pre vis2_l_ )
  **  (IntArray.full sid_pre n_pre sid_l_ )
  **  (IntArray.full scc_next_p_pre 1 (cons (scc_next_v_) ((@nil Z))) )
  **  (IntArray.full order_pre n_pre order_l_low_level_spec )
  **  (IntArray.full fin_pre n_pre fin_l_low_level_spec )
) \/
(
forall (n_pre: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (fin_l_low_level_spec: (@list Z)) (order_l_low_level_spec: (@list Z)) (timer_v_abs_low_level_spec: Z) (vis1_l_abs_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (vis2_m: (@list Z)) (sid_m: (@list Z)) (scc_next_m: Z) (k: Z) (PreH1 : (k >= n_pre)) (PreH2 : (safeExec (pre_kosaraju (g_low_level_spec) (vis1_l_abs_low_level_spec) (vis2_m) (fin_l_low_level_spec) (sid_m) (timer_v_abs_low_level_spec) (scc_next_m)) (kosaraju_scc_from (k)) X_low_level_spec )) (PreH3 : (order_sorted order_l_low_level_spec fin_l_low_level_spec )) (PreH4 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth (j) (order_l_low_level_spec) (0))) /\ ((Znth (j) (order_l_low_level_spec) (0)) < n_pre)))) (PreH5 : (0 <= k)) (PreH6 : (k <= n_pre)) (PreH7 : (n_pre <= INT_MAX)) ,
  TT && emp 
|--
  EX (scc_next_v_: Z) ,
  “ ((cons (scc_next_m) ((@nil Z))) = (cons (scc_next_v_) ((@nil Z)))) ” 
  &&  “ (safeExec (pre_kosaraju (g_low_level_spec) (vis1_l_abs_low_level_spec) (vis2_m) (fin_l_low_level_spec) (sid_m) (timer_v_abs_low_level_spec) (scc_next_v_)) (return (tt)) X_low_level_spec ) ”
  &&  emp
).

Definition kosaraju_scc_partial_solve_wit_1 := 
forall (fin_pre: Z) (order_pre: Z) (scc_next_p_pre: Z) (sid_pre: Z) (vis2_pre: Z) (fadj_pre: Z) (n_pre: Z) (fadj_rows_low_level_spec: (@list (@list Z))) (X_low_level_spec: (unit -> (KSt -> Prop))) (fin_l_low_level_spec: (@list Z)) (order_l_low_level_spec: (@list Z)) (timer_v_abs_low_level_spec: Z) (vis1_l_abs_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (k: Z) (vis2_m: (@list Z)) (sid_m: (@list Z)) (scc_next_m: Z) (PreH1 : (k < n_pre)) (PreH2 : (safeExec (pre_kosaraju (g_low_level_spec) (vis1_l_abs_low_level_spec) (vis2_m) (fin_l_low_level_spec) (sid_m) (timer_v_abs_low_level_spec) (scc_next_m)) (kosaraju_scc_from (k)) X_low_level_spec )) (PreH3 : (order_sorted order_l_low_level_spec fin_l_low_level_spec )) (PreH4 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth (j) (order_l_low_level_spec) (0))) /\ ((Znth (j) (order_l_low_level_spec) (0)) < n_pre)))) (PreH5 : (0 <= k)) (PreH6 : (k <= n_pre)) (PreH7 : (n_pre <= INT_MAX)) ,
  (SllPtrArray.full fadj_pre n_pre fadj_rows_low_level_spec )
  **  (IntArray.full vis2_pre n_pre vis2_m )
  **  (IntArray.full sid_pre n_pre sid_m )
  **  (IntArray.full scc_next_p_pre 1 (cons (scc_next_m) ((@nil Z))) )
  **  (IntArray.full order_pre n_pre order_l_low_level_spec )
  **  (IntArray.full fin_pre n_pre fin_l_low_level_spec )
|--
  “ (k < n_pre) ” 
  &&  “ (safeExec (pre_kosaraju (g_low_level_spec) (vis1_l_abs_low_level_spec) (vis2_m) (fin_l_low_level_spec) (sid_m) (timer_v_abs_low_level_spec) (scc_next_m)) (kosaraju_scc_from (k)) X_low_level_spec ) ” 
  &&  “ (order_sorted order_l_low_level_spec fin_l_low_level_spec ) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth (j) (order_l_low_level_spec) (0))) /\ ((Znth (j) (order_l_low_level_spec) (0)) < n_pre))) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k <= n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ”
  &&  (((order_pre + (k * sizeof(INT) ) )) # Int  |-> (Znth k order_l_low_level_spec 0))
  **  (IntArray.missing_i order_pre k 0 n_pre order_l_low_level_spec )
  **  (SllPtrArray.full fadj_pre n_pre fadj_rows_low_level_spec )
  **  (IntArray.full vis2_pre n_pre vis2_m )
  **  (IntArray.full sid_pre n_pre sid_m )
  **  (IntArray.full scc_next_p_pre 1 (cons (scc_next_m) ((@nil Z))) )
  **  (IntArray.full fin_pre n_pre fin_l_low_level_spec )
.

Definition kosaraju_scc_partial_solve_wit_2 := 
forall (fin_pre: Z) (order_pre: Z) (scc_next_p_pre: Z) (sid_pre: Z) (vis2_pre: Z) (fadj_pre: Z) (n_pre: Z) (fadj_rows_low_level_spec: (@list (@list Z))) (X_low_level_spec: (unit -> (KSt -> Prop))) (fin_l_low_level_spec: (@list Z)) (order_l_low_level_spec: (@list Z)) (timer_v_abs_low_level_spec: Z) (vis1_l_abs_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (vis2_m: (@list Z)) (sid_m: (@list Z)) (scc_next_m: Z) (k: Z) (u: Z) (PreH1 : (0 <= k)) (PreH2 : (k < n_pre)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (u = (Znth (k) (order_l_low_level_spec) (0)))) (PreH5 : (0 <= u)) (PreH6 : (u < n_pre)) (PreH7 : (n_pre <= INT_MAX)) (PreH8 : (safeExec (pre_kosaraju (g_low_level_spec) (vis1_l_abs_low_level_spec) (vis2_m) (fin_l_low_level_spec) (sid_m) (timer_v_abs_low_level_spec) (scc_next_m)) (kosaraju_scc_from (k)) X_low_level_spec )) ,
  (SllPtrArray.full fadj_pre n_pre fadj_rows_low_level_spec )
  **  (IntArray.full vis2_pre n_pre vis2_m )
  **  (IntArray.full sid_pre n_pre sid_m )
  **  (IntArray.full scc_next_p_pre 1 (cons (scc_next_m) ((@nil Z))) )
  **  (IntArray.full order_pre n_pre order_l_low_level_spec )
  **  (IntArray.full fin_pre n_pre fin_l_low_level_spec )
|--
  “ (0 <= k) ” 
  &&  “ (k < n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (u = (Znth (k) (order_l_low_level_spec) (0))) ” 
  &&  “ (0 <= u) ” 
  &&  “ (u < n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (safeExec (pre_kosaraju (g_low_level_spec) (vis1_l_abs_low_level_spec) (vis2_m) (fin_l_low_level_spec) (sid_m) (timer_v_abs_low_level_spec) (scc_next_m)) (kosaraju_scc_from (k)) X_low_level_spec ) ”
  &&  (((vis2_pre + (u * sizeof(INT) ) )) # Int  |-> (Znth u vis2_m 0))
  **  (IntArray.missing_i vis2_pre u 0 n_pre vis2_m )
  **  (SllPtrArray.full fadj_pre n_pre fadj_rows_low_level_spec )
  **  (IntArray.full sid_pre n_pre sid_m )
  **  (IntArray.full scc_next_p_pre 1 (cons (scc_next_m) ((@nil Z))) )
  **  (IntArray.full order_pre n_pre order_l_low_level_spec )
  **  (IntArray.full fin_pre n_pre fin_l_low_level_spec )
.

Definition kosaraju_scc_partial_solve_wit_3 := 
forall (fin_pre: Z) (order_pre: Z) (scc_next_p_pre: Z) (sid_pre: Z) (vis2_pre: Z) (fadj_pre: Z) (n_pre: Z) (fadj_rows_low_level_spec: (@list (@list Z))) (X_low_level_spec: (unit -> (KSt -> Prop))) (fin_l_low_level_spec: (@list Z)) (order_l_low_level_spec: (@list Z)) (timer_v_abs_low_level_spec: Z) (vis1_l_abs_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (vis2_m: (@list Z)) (sid_m: (@list Z)) (scc_next_m: Z) (k: Z) (u: Z) (PreH1 : (0 <= k)) (PreH2 : (k < n_pre)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (0 <= u)) (PreH5 : (u < n_pre)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : ((Znth (u) (vis2_m) (0)) = 0)) (PreH8 : (safeExec (pre_kosaraju (g_low_level_spec) (vis1_l_abs_low_level_spec) (vis2_m) (fin_l_low_level_spec) (sid_m) (timer_v_abs_low_level_spec) (scc_next_m)) (kosaraju_scc_from (k)) X_low_level_spec )) ,
  (SllPtrArray.full fadj_pre n_pre fadj_rows_low_level_spec )
  **  (IntArray.full vis2_pre n_pre vis2_m )
  **  (IntArray.full sid_pre n_pre sid_m )
  **  (IntArray.full scc_next_p_pre 1 (cons (scc_next_m) ((@nil Z))) )
  **  (IntArray.full order_pre n_pre order_l_low_level_spec )
  **  (IntArray.full fin_pre n_pre fin_l_low_level_spec )
|--
  “ (0 <= k) ” 
  &&  “ (k < n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (0 <= u) ” 
  &&  “ (u < n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ ((Znth (u) (vis2_m) (0)) = 0) ” 
  &&  “ (safeExec (pre_kosaraju (g_low_level_spec) (vis1_l_abs_low_level_spec) (vis2_m) (fin_l_low_level_spec) (sid_m) (timer_v_abs_low_level_spec) (scc_next_m)) (kosaraju_scc_from (k)) X_low_level_spec ) ”
  &&  (((scc_next_p_pre + (0 * sizeof(INT) ) )) # Int  |-> (Znth 0 (cons (scc_next_m) ((@nil Z))) 0))
  **  (IntArray.missing_i scc_next_p_pre 0 0 1 (cons (scc_next_m) ((@nil Z))) )
  **  (SllPtrArray.full fadj_pre n_pre fadj_rows_low_level_spec )
  **  (IntArray.full vis2_pre n_pre vis2_m )
  **  (IntArray.full sid_pre n_pre sid_m )
  **  (IntArray.full order_pre n_pre order_l_low_level_spec )
  **  (IntArray.full fin_pre n_pre fin_l_low_level_spec )
.

Definition kosaraju_scc_partial_solve_wit_4 := 
forall (fin_pre: Z) (order_pre: Z) (scc_next_p_pre: Z) (sid_pre: Z) (vis2_pre: Z) (fadj_pre: Z) (n_pre: Z) (fadj_rows_low_level_spec: (@list (@list Z))) (X_low_level_spec: (unit -> (KSt -> Prop))) (fin_l_low_level_spec: (@list Z)) (order_l_low_level_spec: (@list Z)) (timer_v_abs_low_level_spec: Z) (vis1_l_abs_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (vis2_m: (@list Z)) (sid_m: (@list Z)) (scc_next_m: Z) (k: Z) (u: Z) (PreH1 : (0 <= k)) (PreH2 : (k < n_pre)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (0 <= u)) (PreH5 : (u < n_pre)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : ((Znth (u) (vis2_m) (0)) = 0)) (PreH8 : (safeExec (pre_kosaraju (g_low_level_spec) (vis1_l_abs_low_level_spec) (vis2_m) (fin_l_low_level_spec) (sid_m) (timer_v_abs_low_level_spec) (scc_next_m)) (kosaraju_scc_from (k)) X_low_level_spec )) ,
  (IntArray.full scc_next_p_pre 1 (cons (scc_next_m) ((@nil Z))) )
  **  (SllPtrArray.full fadj_pre n_pre fadj_rows_low_level_spec )
  **  (IntArray.full vis2_pre n_pre vis2_m )
  **  (IntArray.full sid_pre n_pre sid_m )
  **  (IntArray.full order_pre n_pre order_l_low_level_spec )
  **  (IntArray.full fin_pre n_pre fin_l_low_level_spec )
|--
  “ (0 <= k) ” 
  &&  “ (k < n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (0 <= u) ” 
  &&  “ (u < n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ ((Znth (u) (vis2_m) (0)) = 0) ” 
  &&  “ (safeExec (pre_kosaraju (g_low_level_spec) (vis1_l_abs_low_level_spec) (vis2_m) (fin_l_low_level_spec) (sid_m) (timer_v_abs_low_level_spec) (scc_next_m)) (kosaraju_scc_from (k)) X_low_level_spec ) ”
  &&  (((sid_pre + (u * sizeof(INT) ) )) # Int  |->_)
  **  (IntArray.missing_i sid_pre u 0 n_pre sid_m )
  **  (IntArray.full scc_next_p_pre 1 (cons (scc_next_m) ((@nil Z))) )
  **  (SllPtrArray.full fadj_pre n_pre fadj_rows_low_level_spec )
  **  (IntArray.full vis2_pre n_pre vis2_m )
  **  (IntArray.full order_pre n_pre order_l_low_level_spec )
  **  (IntArray.full fin_pre n_pre fin_l_low_level_spec )
.

Definition kosaraju_scc_partial_solve_wit_5 := 
forall (fin_pre: Z) (order_pre: Z) (scc_next_p_pre: Z) (sid_pre: Z) (vis2_pre: Z) (fadj_pre: Z) (n_pre: Z) (fadj_rows_low_level_spec: (@list (@list Z))) (X_low_level_spec: (unit -> (KSt -> Prop))) (fin_l_low_level_spec: (@list Z)) (order_l_low_level_spec: (@list Z)) (timer_v_abs_low_level_spec: Z) (vis1_l_abs_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (vis2_m: (@list Z)) (sid_m: (@list Z)) (scc_next_m: Z) (k: Z) (u: Z) (PreH1 : (0 <= k)) (PreH2 : (k < n_pre)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (0 <= u)) (PreH5 : (u < n_pre)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : ((Znth (u) (vis2_m) (0)) = 0)) (PreH8 : (safeExec (pre_kosaraju (g_low_level_spec) (vis1_l_abs_low_level_spec) (vis2_m) (fin_l_low_level_spec) (sid_m) (timer_v_abs_low_level_spec) (scc_next_m)) (kosaraju_scc_from (k)) X_low_level_spec )) ,
  (IntArray.full sid_pre n_pre (replace_Znth (u) ((Znth 0 (cons (scc_next_m) ((@nil Z))) 0)) (sid_m)) )
  **  (IntArray.full scc_next_p_pre 1 (cons (scc_next_m) ((@nil Z))) )
  **  (SllPtrArray.full fadj_pre n_pre fadj_rows_low_level_spec )
  **  (IntArray.full vis2_pre n_pre vis2_m )
  **  (IntArray.full order_pre n_pre order_l_low_level_spec )
  **  (IntArray.full fin_pre n_pre fin_l_low_level_spec )
|--
  “ (0 <= k) ” 
  &&  “ (k < n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (0 <= u) ” 
  &&  “ (u < n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ ((Znth (u) (vis2_m) (0)) = 0) ” 
  &&  “ (safeExec (pre_kosaraju (g_low_level_spec) (vis1_l_abs_low_level_spec) (vis2_m) (fin_l_low_level_spec) (sid_m) (timer_v_abs_low_level_spec) (scc_next_m)) (kosaraju_scc_from (k)) X_low_level_spec ) ”
  &&  (((scc_next_p_pre + (0 * sizeof(INT) ) )) # Int  |-> (Znth 0 (cons (scc_next_m) ((@nil Z))) 0))
  **  (IntArray.missing_i scc_next_p_pre 0 0 1 (cons (scc_next_m) ((@nil Z))) )
  **  (IntArray.full sid_pre n_pre (replace_Znth (u) ((Znth 0 (cons (scc_next_m) ((@nil Z))) 0)) (sid_m)) )
  **  (SllPtrArray.full fadj_pre n_pre fadj_rows_low_level_spec )
  **  (IntArray.full vis2_pre n_pre vis2_m )
  **  (IntArray.full order_pre n_pre order_l_low_level_spec )
  **  (IntArray.full fin_pre n_pre fin_l_low_level_spec )
.

Definition kosaraju_scc_partial_solve_wit_6 := 
forall (fin_pre: Z) (order_pre: Z) (scc_next_p_pre: Z) (sid_pre: Z) (vis2_pre: Z) (fadj_pre: Z) (n_pre: Z) (fadj_rows_low_level_spec: (@list (@list Z))) (X_low_level_spec: (unit -> (KSt -> Prop))) (fin_l_low_level_spec: (@list Z)) (order_l_low_level_spec: (@list Z)) (timer_v_abs_low_level_spec: Z) (vis1_l_abs_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (vis2_m: (@list Z)) (sid_m: (@list Z)) (scc_next_m: Z) (k: Z) (u: Z) (PreH1 : (0 <= k)) (PreH2 : (k < n_pre)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (0 <= u)) (PreH5 : (u < n_pre)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : ((Znth (u) (vis2_m) (0)) = 0)) (PreH8 : (safeExec (pre_kosaraju (g_low_level_spec) (vis1_l_abs_low_level_spec) (vis2_m) (fin_l_low_level_spec) (sid_m) (timer_v_abs_low_level_spec) (scc_next_m)) (kosaraju_scc_from (k)) X_low_level_spec )) ,
  (IntArray.full scc_next_p_pre 1 (cons (scc_next_m) ((@nil Z))) )
  **  (IntArray.full sid_pre n_pre (replace_Znth (u) ((Znth 0 (cons (scc_next_m) ((@nil Z))) 0)) (sid_m)) )
  **  (SllPtrArray.full fadj_pre n_pre fadj_rows_low_level_spec )
  **  (IntArray.full vis2_pre n_pre vis2_m )
  **  (IntArray.full order_pre n_pre order_l_low_level_spec )
  **  (IntArray.full fin_pre n_pre fin_l_low_level_spec )
|--
  “ (0 <= k) ” 
  &&  “ (k < n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (0 <= u) ” 
  &&  “ (u < n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ ((Znth (u) (vis2_m) (0)) = 0) ” 
  &&  “ (safeExec (pre_kosaraju (g_low_level_spec) (vis1_l_abs_low_level_spec) (vis2_m) (fin_l_low_level_spec) (sid_m) (timer_v_abs_low_level_spec) (scc_next_m)) (kosaraju_scc_from (k)) X_low_level_spec ) ”
  &&  (((scc_next_p_pre + (0 * sizeof(INT) ) )) # Int  |->_)
  **  (IntArray.missing_i scc_next_p_pre 0 0 1 (cons (scc_next_m) ((@nil Z))) )
  **  (IntArray.full sid_pre n_pre (replace_Znth (u) ((Znth 0 (cons (scc_next_m) ((@nil Z))) 0)) (sid_m)) )
  **  (SllPtrArray.full fadj_pre n_pre fadj_rows_low_level_spec )
  **  (IntArray.full vis2_pre n_pre vis2_m )
  **  (IntArray.full order_pre n_pre order_l_low_level_spec )
  **  (IntArray.full fin_pre n_pre fin_l_low_level_spec )
.

Definition kosaraju_scc_partial_solve_wit_7_pure := 
(
forall (fin_pre: Z) (order_pre: Z) (scc_next_p_pre: Z) (sid_pre: Z) (vis2_pre: Z) (fadj_pre: Z) (n_pre: Z) (fadj_rows_low_level_spec: (@list (@list Z))) (X_low_level_spec: (unit -> (KSt -> Prop))) (fin_l_low_level_spec: (@list Z)) (order_l_low_level_spec: (@list Z)) (timer_v_abs_low_level_spec: Z) (vis1_l_abs_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (vis2_m: (@list Z)) (sid_m: (@list Z)) (scc_next_m: Z) (k: Z) (u: Z) (PreH1 : (0 <= k)) (PreH2 : (k < n_pre)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (0 <= u)) (PreH5 : (u < n_pre)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : ((Znth (u) (vis2_m) (0)) = 0)) (PreH8 : (safeExec (pre_kosaraju (g_low_level_spec) (vis1_l_abs_low_level_spec) (vis2_m) (fin_l_low_level_spec) (sid_m) (timer_v_abs_low_level_spec) (scc_next_m)) (kosaraju_scc_from (k)) X_low_level_spec )) ,
  (IntArray.full scc_next_p_pre 1 (replace_Znth (0) (((Znth 0 (cons (scc_next_m) ((@nil Z))) 0) + 1 )) ((cons (scc_next_m) ((@nil Z))))) )
  **  (IntArray.full sid_pre n_pre (replace_Znth (u) ((Znth 0 (cons (scc_next_m) ((@nil Z))) 0)) (sid_m)) )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "fadj" ) )) # Ptr  |-> fadj_pre)
  **  ((( &( "vis2" ) )) # Ptr  |-> vis2_pre)
  **  ((( &( "sid" ) )) # Ptr  |-> sid_pre)
  **  ((( &( "scc_next_p" ) )) # Ptr  |-> scc_next_p_pre)
  **  ((( &( "order" ) )) # Ptr  |-> order_pre)
  **  ((( &( "fin" ) )) # Ptr  |-> fin_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "u" ) )) # Int  |-> u)
  **  (SllPtrArray.full fadj_pre n_pre fadj_rows_low_level_spec )
  **  (IntArray.full vis2_pre n_pre vis2_m )
  **  (IntArray.full order_pre n_pre order_l_low_level_spec )
  **  (IntArray.full fin_pre n_pre fin_l_low_level_spec )
|--
  “ (0 <= u) ” 
  &&  “ (u < n_pre) ” 
  &&  “ (0 <= u) ” 
  &&  “ (u < n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (safeExec (pre_dfs2 (g_low_level_spec) (vis2_m) (sid_m)) (dfs_scc (u) (u)) X_low_level_spec ) ” 
  &&  “ ((replace_Znth (u) ((Znth 0 (cons (scc_next_m) ((@nil Z))) 0)) (sid_m)) = sid_m) ”
) \/
(
forall (fin_pre: Z) (order_pre: Z) (scc_next_p_pre: Z) (sid_pre: Z) (vis2_pre: Z) (fadj_pre: Z) (n_pre: Z) (fadj_rows_low_level_spec: (@list (@list Z))) (X_low_level_spec: (unit -> (KSt -> Prop))) (fin_l_low_level_spec: (@list Z)) (order_l_low_level_spec: (@list Z)) (timer_v_abs_low_level_spec: Z) (vis1_l_abs_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (vis2_m: (@list Z)) (sid_m: (@list Z)) (scc_next_m: Z) (k: Z) (u: Z) (PreH1 : (u <= INT_MAX)) (PreH2 : (k <= INT_MAX)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (u >= INT_MIN)) (PreH5 : (k >= INT_MIN)) (PreH6 : (n_pre >= INT_MIN)) (PreH7 : (0 <= k)) (PreH8 : (k < n_pre)) (PreH9 : (n_pre <= INT_MAX)) (PreH10 : (0 <= u)) (PreH11 : (u < n_pre)) (PreH12 : (n_pre <= INT_MAX)) (PreH13 : ((Znth (u) (vis2_m) (0)) = 0)) (PreH14 : (safeExec (pre_kosaraju (g_low_level_spec) (vis1_l_abs_low_level_spec) (vis2_m) (fin_l_low_level_spec) (sid_m) (timer_v_abs_low_level_spec) (scc_next_m)) (kosaraju_scc_from (k)) X_low_level_spec )) ,
  (IntArray.full scc_next_p_pre 1 (replace_Znth (0) (((Znth 0 (cons (scc_next_m) ((@nil Z))) 0) + 1 )) ((cons (scc_next_m) ((@nil Z))))) )
  **  (IntArray.full sid_pre n_pre (replace_Znth (u) ((Znth 0 (cons (scc_next_m) ((@nil Z))) 0)) (sid_m)) )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "fadj" ) )) # Ptr  |-> fadj_pre)
  **  ((( &( "vis2" ) )) # Ptr  |-> vis2_pre)
  **  ((( &( "sid" ) )) # Ptr  |-> sid_pre)
  **  ((( &( "scc_next_p" ) )) # Ptr  |-> scc_next_p_pre)
  **  ((( &( "order" ) )) # Ptr  |-> order_pre)
  **  ((( &( "fin" ) )) # Ptr  |-> fin_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "u" ) )) # Int  |-> u)
  **  (SllPtrArray.full fadj_pre n_pre fadj_rows_low_level_spec )
  **  (IntArray.full vis2_pre n_pre vis2_m )
  **  (IntArray.full order_pre n_pre order_l_low_level_spec )
  **  (IntArray.full fin_pre n_pre fin_l_low_level_spec )
|--
  “ ((replace_Znth (u) ((Znth 0 (cons (scc_next_m) ((@nil Z))) 0)) (sid_m)) = sid_m) ” 
  &&  “ (safeExec (pre_dfs2 (g_low_level_spec) (vis2_m) (sid_m)) (dfs_scc (u) (u)) X_low_level_spec ) ”
).

Definition kosaraju_scc_partial_solve_wit_7_pure_split_goal_1 := 
forall (fin_pre: Z) (order_pre: Z) (scc_next_p_pre: Z) (sid_pre: Z) (vis2_pre: Z) (fadj_pre: Z) (n_pre: Z) (fadj_rows_low_level_spec: (@list (@list Z))) (X_low_level_spec: (unit -> (KSt -> Prop))) (fin_l_low_level_spec: (@list Z)) (order_l_low_level_spec: (@list Z)) (timer_v_abs_low_level_spec: Z) (vis1_l_abs_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (vis2_m: (@list Z)) (sid_m: (@list Z)) (scc_next_m: Z) (k: Z) (u: Z) (PreH1 : (u <= INT_MAX)) (PreH2 : (k <= INT_MAX)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (u >= INT_MIN)) (PreH5 : (k >= INT_MIN)) (PreH6 : (n_pre >= INT_MIN)) (PreH7 : (0 <= k)) (PreH8 : (k < n_pre)) (PreH9 : (n_pre <= INT_MAX)) (PreH10 : (0 <= u)) (PreH11 : (u < n_pre)) (PreH12 : (n_pre <= INT_MAX)) (PreH13 : ((Znth (u) (vis2_m) (0)) = 0)) (PreH14 : (safeExec (pre_kosaraju (g_low_level_spec) (vis1_l_abs_low_level_spec) (vis2_m) (fin_l_low_level_spec) (sid_m) (timer_v_abs_low_level_spec) (scc_next_m)) (kosaraju_scc_from (k)) X_low_level_spec )) ,
  (IntArray.full scc_next_p_pre 1 (replace_Znth (0) (((Znth 0 (cons (scc_next_m) ((@nil Z))) 0) + 1 )) ((cons (scc_next_m) ((@nil Z))))) )
  **  (IntArray.full sid_pre n_pre (replace_Znth (u) ((Znth 0 (cons (scc_next_m) ((@nil Z))) 0)) (sid_m)) )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "fadj" ) )) # Ptr  |-> fadj_pre)
  **  ((( &( "vis2" ) )) # Ptr  |-> vis2_pre)
  **  ((( &( "sid" ) )) # Ptr  |-> sid_pre)
  **  ((( &( "scc_next_p" ) )) # Ptr  |-> scc_next_p_pre)
  **  ((( &( "order" ) )) # Ptr  |-> order_pre)
  **  ((( &( "fin" ) )) # Ptr  |-> fin_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "u" ) )) # Int  |-> u)
  **  (SllPtrArray.full fadj_pre n_pre fadj_rows_low_level_spec )
  **  (IntArray.full vis2_pre n_pre vis2_m )
  **  (IntArray.full order_pre n_pre order_l_low_level_spec )
  **  (IntArray.full fin_pre n_pre fin_l_low_level_spec )
|--
  “ ((replace_Znth (u) ((Znth 0 (cons (scc_next_m) ((@nil Z))) 0)) (sid_m)) = sid_m) ”
.

Definition kosaraju_scc_partial_solve_wit_7_pure_split_goal_2 := 
forall (fin_pre: Z) (order_pre: Z) (scc_next_p_pre: Z) (sid_pre: Z) (vis2_pre: Z) (fadj_pre: Z) (n_pre: Z) (fadj_rows_low_level_spec: (@list (@list Z))) (X_low_level_spec: (unit -> (KSt -> Prop))) (fin_l_low_level_spec: (@list Z)) (order_l_low_level_spec: (@list Z)) (timer_v_abs_low_level_spec: Z) (vis1_l_abs_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (vis2_m: (@list Z)) (sid_m: (@list Z)) (scc_next_m: Z) (k: Z) (u: Z) (PreH1 : (u <= INT_MAX)) (PreH2 : (k <= INT_MAX)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (u >= INT_MIN)) (PreH5 : (k >= INT_MIN)) (PreH6 : (n_pre >= INT_MIN)) (PreH7 : (0 <= k)) (PreH8 : (k < n_pre)) (PreH9 : (n_pre <= INT_MAX)) (PreH10 : (0 <= u)) (PreH11 : (u < n_pre)) (PreH12 : (n_pre <= INT_MAX)) (PreH13 : ((Znth (u) (vis2_m) (0)) = 0)) (PreH14 : (safeExec (pre_kosaraju (g_low_level_spec) (vis1_l_abs_low_level_spec) (vis2_m) (fin_l_low_level_spec) (sid_m) (timer_v_abs_low_level_spec) (scc_next_m)) (kosaraju_scc_from (k)) X_low_level_spec )) ,
  (IntArray.full scc_next_p_pre 1 (replace_Znth (0) (((Znth 0 (cons (scc_next_m) ((@nil Z))) 0) + 1 )) ((cons (scc_next_m) ((@nil Z))))) )
  **  (IntArray.full sid_pre n_pre (replace_Znth (u) ((Znth 0 (cons (scc_next_m) ((@nil Z))) 0)) (sid_m)) )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "fadj" ) )) # Ptr  |-> fadj_pre)
  **  ((( &( "vis2" ) )) # Ptr  |-> vis2_pre)
  **  ((( &( "sid" ) )) # Ptr  |-> sid_pre)
  **  ((( &( "scc_next_p" ) )) # Ptr  |-> scc_next_p_pre)
  **  ((( &( "order" ) )) # Ptr  |-> order_pre)
  **  ((( &( "fin" ) )) # Ptr  |-> fin_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "u" ) )) # Int  |-> u)
  **  (SllPtrArray.full fadj_pre n_pre fadj_rows_low_level_spec )
  **  (IntArray.full vis2_pre n_pre vis2_m )
  **  (IntArray.full order_pre n_pre order_l_low_level_spec )
  **  (IntArray.full fin_pre n_pre fin_l_low_level_spec )
|--
  “ (safeExec (pre_dfs2 (g_low_level_spec) (vis2_m) (sid_m)) (dfs_scc (u) (u)) X_low_level_spec ) ”
.

Definition kosaraju_scc_partial_solve_wit_7_aux := 
forall (fin_pre: Z) (order_pre: Z) (scc_next_p_pre: Z) (sid_pre: Z) (vis2_pre: Z) (fadj_pre: Z) (n_pre: Z) (fadj_rows_low_level_spec: (@list (@list Z))) (X_low_level_spec: (unit -> (KSt -> Prop))) (fin_l_low_level_spec: (@list Z)) (order_l_low_level_spec: (@list Z)) (timer_v_abs_low_level_spec: Z) (vis1_l_abs_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (vis2_m: (@list Z)) (sid_m: (@list Z)) (scc_next_m: Z) (k: Z) (u: Z) (PreH1 : (0 <= k)) (PreH2 : (k < n_pre)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (0 <= u)) (PreH5 : (u < n_pre)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : ((Znth (u) (vis2_m) (0)) = 0)) (PreH8 : (safeExec (pre_kosaraju (g_low_level_spec) (vis1_l_abs_low_level_spec) (vis2_m) (fin_l_low_level_spec) (sid_m) (timer_v_abs_low_level_spec) (scc_next_m)) (kosaraju_scc_from (k)) X_low_level_spec )) ,
  (IntArray.full scc_next_p_pre 1 (replace_Znth (0) (((Znth 0 (cons (scc_next_m) ((@nil Z))) 0) + 1 )) ((cons (scc_next_m) ((@nil Z))))) )
  **  (IntArray.full sid_pre n_pre (replace_Znth (u) ((Znth 0 (cons (scc_next_m) ((@nil Z))) 0)) (sid_m)) )
  **  (SllPtrArray.full fadj_pre n_pre fadj_rows_low_level_spec )
  **  (IntArray.full vis2_pre n_pre vis2_m )
  **  (IntArray.full order_pre n_pre order_l_low_level_spec )
  **  (IntArray.full fin_pre n_pre fin_l_low_level_spec )
|--
  “ (0 <= u) ” 
  &&  “ (u < n_pre) ” 
  &&  “ (0 <= u) ” 
  &&  “ (u < n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (safeExec (pre_dfs2 (g_low_level_spec) (vis2_m) (sid_m)) (dfs_scc (u) (u)) X_low_level_spec ) ” 
  &&  “ ((replace_Znth (u) ((Znth 0 (cons (scc_next_m) ((@nil Z))) 0)) (sid_m)) = sid_m) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k < n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (0 <= u) ” 
  &&  “ (u < n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ ((Znth (u) (vis2_m) (0)) = 0) ” 
  &&  “ (safeExec (pre_kosaraju (g_low_level_spec) (vis1_l_abs_low_level_spec) (vis2_m) (fin_l_low_level_spec) (sid_m) (timer_v_abs_low_level_spec) (scc_next_m)) (kosaraju_scc_from (k)) X_low_level_spec ) ”
  &&  (SllPtrArray.full fadj_pre n_pre fadj_rows_low_level_spec )
  **  (IntArray.full vis2_pre n_pre vis2_m )
  **  (IntArray.full sid_pre n_pre sid_m )
  **  (IntArray.full scc_next_p_pre 1 (replace_Znth (0) (((Znth 0 (cons (scc_next_m) ((@nil Z))) 0) + 1 )) ((cons (scc_next_m) ((@nil Z))))) )
  **  (IntArray.full order_pre n_pre order_l_low_level_spec )
  **  (IntArray.full fin_pre n_pre fin_l_low_level_spec )
.

Definition kosaraju_scc_partial_solve_wit_7 := kosaraju_scc_partial_solve_wit_7_pure -> kosaraju_scc_partial_solve_wit_7_aux.

(*----- Function kosaraju_run -----*)

Definition kosaraju_run_return_wit_1 := 
(
forall (order_pre: Z) (scc_next_p_pre: Z) (timer_p_pre: Z) (sid_pre: Z) (fin_pre: Z) (vis2_pre: Z) (vis1_pre: Z) (fadj_pre: Z) (radj_pre: Z) (n_pre: Z) (fadj_rows_low_level_spec: (@list (@list Z))) (radj_rows_low_level_spec: (@list (@list Z))) (X_low_level_spec: (unit -> (KSt -> Prop))) (order_l_low_level_spec: (@list Z)) (timer_v_low_level_spec: Z) (fin_l_low_level_spec: (@list Z)) (vis1_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (vis1_l__2: (@list Z)) (timer_v__2: Z) (vis2_l__2: (@list Z)) (sid_l__2: (@list Z)) (scc_next_v__2: Z) (PreH1 : (safeExec (pre_kosaraju (g_low_level_spec) (vis1_l_low_level_spec) (vis2_l__2) (fin_l_low_level_spec) (sid_l__2) (timer_v_low_level_spec) (scc_next_v__2)) (return (tt)) X_low_level_spec )) (PreH2 : (order_sorted order_l_low_level_spec fin_l_low_level_spec )) (PreH3 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth (j) (order_l_low_level_spec) (0))) /\ ((Znth (j) (order_l_low_level_spec) (0)) < n_pre)))) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre <= INT_MAX)) ,
  (SllPtrArray.full fadj_pre n_pre fadj_rows_low_level_spec )
  **  (IntArray.full vis2_pre n_pre vis2_l__2 )
  **  (IntArray.full sid_pre n_pre sid_l__2 )
  **  (IntArray.full scc_next_p_pre 1 (cons (scc_next_v__2) ((@nil Z))) )
  **  (IntArray.full order_pre n_pre order_l_low_level_spec )
  **  (IntArray.full fin_pre n_pre fin_l_low_level_spec )
  **  (SllPtrArray.full radj_pre n_pre radj_rows_low_level_spec )
  **  (IntArray.full vis1_pre n_pre vis1_l__2 )
  **  (IntArray.full timer_p_pre 1 (cons (timer_v__2) ((@nil Z))) )
|--
  EX (vis1_l_: (@list Z))  (vis2_l_: (@list Z))  (fin_l_: (@list Z))  (sid_l_: (@list Z))  (timer_v_: Z)  (scc_next_v_: Z) ,
  “ (safeExec (pre_kosaraju (g_low_level_spec) (vis1_l_) (vis2_l_) (fin_l_) (sid_l_) (timer_v_) (scc_next_v_)) (return (tt)) X_low_level_spec ) ”
  &&  (SllPtrArray.full radj_pre n_pre radj_rows_low_level_spec )
  **  (SllPtrArray.full fadj_pre n_pre fadj_rows_low_level_spec )
  **  (IntArray.full vis1_pre n_pre vis1_l_ )
  **  (IntArray.full vis2_pre n_pre vis2_l_ )
  **  (IntArray.full fin_pre n_pre fin_l_ )
  **  (IntArray.full sid_pre n_pre sid_l_ )
  **  (IntArray.full timer_p_pre 1 (cons (timer_v_) ((@nil Z))) )
  **  (IntArray.full scc_next_p_pre 1 (cons (scc_next_v_) ((@nil Z))) )
  **  (IntArray.full order_pre n_pre order_l_low_level_spec )
) \/
(
forall (n_pre: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (order_l_low_level_spec: (@list Z)) (timer_v_low_level_spec: Z) (fin_l_low_level_spec: (@list Z)) (vis1_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (vis1_l__2: (@list Z)) (timer_v__2: Z) (vis2_l__2: (@list Z)) (sid_l__2: (@list Z)) (scc_next_v__2: Z) (PreH1 : (safeExec (pre_kosaraju (g_low_level_spec) (vis1_l_low_level_spec) (vis2_l__2) (fin_l_low_level_spec) (sid_l__2) (timer_v_low_level_spec) (scc_next_v__2)) (return (tt)) X_low_level_spec )) (PreH2 : (order_sorted order_l_low_level_spec fin_l_low_level_spec )) (PreH3 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth (j) (order_l_low_level_spec) (0))) /\ ((Znth (j) (order_l_low_level_spec) (0)) < n_pre)))) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre <= INT_MAX)) ,
  TT && emp 
|--
  EX (timer_v_: Z)  (scc_next_v_: Z) ,
  “ ((cons (timer_v__2) ((@nil Z))) = (cons (timer_v_) ((@nil Z)))) ” 
  &&  “ ((cons (scc_next_v__2) ((@nil Z))) = (cons (scc_next_v_) ((@nil Z)))) ” 
  &&  “ (safeExec (pre_kosaraju (g_low_level_spec) (vis1_l__2) (vis2_l__2) (fin_l_low_level_spec) (sid_l__2) (timer_v_) (scc_next_v_)) (return (tt)) X_low_level_spec ) ”
  &&  emp
).

Definition kosaraju_run_partial_solve_wit_1_pure := 
(
forall (order_pre: Z) (scc_next_p_pre: Z) (timer_p_pre: Z) (sid_pre: Z) (fin_pre: Z) (vis2_pre: Z) (vis1_pre: Z) (fadj_pre: Z) (radj_pre: Z) (n_pre: Z) (fadj_rows_low_level_spec: (@list (@list Z))) (radj_rows_low_level_spec: (@list (@list Z))) (X_low_level_spec: (unit -> (KSt -> Prop))) (order_l_low_level_spec: (@list Z)) (scc_next_v_low_level_spec: Z) (timer_v_low_level_spec: Z) (sid_l_low_level_spec: (@list Z)) (fin_l_low_level_spec: (@list Z)) (vis2_l_low_level_spec: (@list Z)) (vis1_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (PreH1 : (safeExec (pre_kosaraju (g_low_level_spec) (vis1_l_low_level_spec) (vis2_l_low_level_spec) (fin_l_low_level_spec) (sid_l_low_level_spec) (timer_v_low_level_spec) (scc_next_v_low_level_spec)) kosaraju_monad X_low_level_spec )) (PreH2 : (order_sorted order_l_low_level_spec fin_l_low_level_spec )) (PreH3 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth (j) (order_l_low_level_spec) (0))) /\ ((Znth (j) (order_l_low_level_spec) (0)) < n_pre)))) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre <= INT_MAX)) ,
  ((( &( "order" ) )) # Ptr  |-> order_pre)
  **  ((( &( "scc_next_p" ) )) # Ptr  |-> scc_next_p_pre)
  **  ((( &( "timer_p" ) )) # Ptr  |-> timer_p_pre)
  **  ((( &( "sid" ) )) # Ptr  |-> sid_pre)
  **  ((( &( "fin" ) )) # Ptr  |-> fin_pre)
  **  ((( &( "vis2" ) )) # Ptr  |-> vis2_pre)
  **  ((( &( "vis1" ) )) # Ptr  |-> vis1_pre)
  **  ((( &( "fadj" ) )) # Ptr  |-> fadj_pre)
  **  ((( &( "radj" ) )) # Ptr  |-> radj_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (SllPtrArray.full radj_pre n_pre radj_rows_low_level_spec )
  **  (SllPtrArray.full fadj_pre n_pre fadj_rows_low_level_spec )
  **  (IntArray.full vis1_pre n_pre vis1_l_low_level_spec )
  **  (IntArray.full vis2_pre n_pre vis2_l_low_level_spec )
  **  (IntArray.full fin_pre n_pre fin_l_low_level_spec )
  **  (IntArray.full sid_pre n_pre sid_l_low_level_spec )
  **  (IntArray.full timer_p_pre 1 (cons (timer_v_low_level_spec) ((@nil Z))) )
  **  (IntArray.full scc_next_p_pre 1 (cons (scc_next_v_low_level_spec) ((@nil Z))) )
  **  (IntArray.full order_pre n_pre order_l_low_level_spec )
|--
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (safeExec (pre_kosaraju (g_low_level_spec) (vis1_l_low_level_spec) (vis2_l_low_level_spec) (fin_l_low_level_spec) (sid_l_low_level_spec) (timer_v_low_level_spec) (scc_next_v_low_level_spec)) kosaraju_finish_monad X_low_level_spec ) ”
) \/
(
forall (order_pre: Z) (scc_next_p_pre: Z) (timer_p_pre: Z) (sid_pre: Z) (fin_pre: Z) (vis2_pre: Z) (vis1_pre: Z) (fadj_pre: Z) (radj_pre: Z) (n_pre: Z) (fadj_rows_low_level_spec: (@list (@list Z))) (radj_rows_low_level_spec: (@list (@list Z))) (X_low_level_spec: (unit -> (KSt -> Prop))) (order_l_low_level_spec: (@list Z)) (scc_next_v_low_level_spec: Z) (timer_v_low_level_spec: Z) (sid_l_low_level_spec: (@list Z)) (fin_l_low_level_spec: (@list Z)) (vis2_l_low_level_spec: (@list Z)) (vis1_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (PreH1 : (n_pre <= INT_MAX)) (PreH2 : (n_pre >= INT_MIN)) (PreH3 : (safeExec (pre_kosaraju (g_low_level_spec) (vis1_l_low_level_spec) (vis2_l_low_level_spec) (fin_l_low_level_spec) (sid_l_low_level_spec) (timer_v_low_level_spec) (scc_next_v_low_level_spec)) kosaraju_monad X_low_level_spec )) (PreH4 : (order_sorted order_l_low_level_spec fin_l_low_level_spec )) (PreH5 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth (j) (order_l_low_level_spec) (0))) /\ ((Znth (j) (order_l_low_level_spec) (0)) < n_pre)))) (PreH6 : (0 <= n_pre)) (PreH7 : (n_pre <= INT_MAX)) ,
  ((( &( "order" ) )) # Ptr  |-> order_pre)
  **  ((( &( "scc_next_p" ) )) # Ptr  |-> scc_next_p_pre)
  **  ((( &( "timer_p" ) )) # Ptr  |-> timer_p_pre)
  **  ((( &( "sid" ) )) # Ptr  |-> sid_pre)
  **  ((( &( "fin" ) )) # Ptr  |-> fin_pre)
  **  ((( &( "vis2" ) )) # Ptr  |-> vis2_pre)
  **  ((( &( "vis1" ) )) # Ptr  |-> vis1_pre)
  **  ((( &( "fadj" ) )) # Ptr  |-> fadj_pre)
  **  ((( &( "radj" ) )) # Ptr  |-> radj_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (SllPtrArray.full radj_pre n_pre radj_rows_low_level_spec )
  **  (SllPtrArray.full fadj_pre n_pre fadj_rows_low_level_spec )
  **  (IntArray.full vis1_pre n_pre vis1_l_low_level_spec )
  **  (IntArray.full vis2_pre n_pre vis2_l_low_level_spec )
  **  (IntArray.full fin_pre n_pre fin_l_low_level_spec )
  **  (IntArray.full sid_pre n_pre sid_l_low_level_spec )
  **  (IntArray.full timer_p_pre 1 (cons (timer_v_low_level_spec) ((@nil Z))) )
  **  (IntArray.full scc_next_p_pre 1 (cons (scc_next_v_low_level_spec) ((@nil Z))) )
  **  (IntArray.full order_pre n_pre order_l_low_level_spec )
|--
  “ (safeExec (pre_kosaraju (g_low_level_spec) (vis1_l_low_level_spec) (vis2_l_low_level_spec) (fin_l_low_level_spec) (sid_l_low_level_spec) (timer_v_low_level_spec) (scc_next_v_low_level_spec)) kosaraju_finish_monad X_low_level_spec ) ”
).

Definition kosaraju_run_partial_solve_wit_1_pure_split_goal_1 := 
forall (order_pre: Z) (scc_next_p_pre: Z) (timer_p_pre: Z) (sid_pre: Z) (fin_pre: Z) (vis2_pre: Z) (vis1_pre: Z) (fadj_pre: Z) (radj_pre: Z) (n_pre: Z) (fadj_rows_low_level_spec: (@list (@list Z))) (radj_rows_low_level_spec: (@list (@list Z))) (X_low_level_spec: (unit -> (KSt -> Prop))) (order_l_low_level_spec: (@list Z)) (scc_next_v_low_level_spec: Z) (timer_v_low_level_spec: Z) (sid_l_low_level_spec: (@list Z)) (fin_l_low_level_spec: (@list Z)) (vis2_l_low_level_spec: (@list Z)) (vis1_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (PreH1 : (n_pre <= INT_MAX)) (PreH2 : (n_pre >= INT_MIN)) (PreH3 : (safeExec (pre_kosaraju (g_low_level_spec) (vis1_l_low_level_spec) (vis2_l_low_level_spec) (fin_l_low_level_spec) (sid_l_low_level_spec) (timer_v_low_level_spec) (scc_next_v_low_level_spec)) kosaraju_monad X_low_level_spec )) (PreH4 : (order_sorted order_l_low_level_spec fin_l_low_level_spec )) (PreH5 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth (j) (order_l_low_level_spec) (0))) /\ ((Znth (j) (order_l_low_level_spec) (0)) < n_pre)))) (PreH6 : (0 <= n_pre)) (PreH7 : (n_pre <= INT_MAX)) ,
  ((( &( "order" ) )) # Ptr  |-> order_pre)
  **  ((( &( "scc_next_p" ) )) # Ptr  |-> scc_next_p_pre)
  **  ((( &( "timer_p" ) )) # Ptr  |-> timer_p_pre)
  **  ((( &( "sid" ) )) # Ptr  |-> sid_pre)
  **  ((( &( "fin" ) )) # Ptr  |-> fin_pre)
  **  ((( &( "vis2" ) )) # Ptr  |-> vis2_pre)
  **  ((( &( "vis1" ) )) # Ptr  |-> vis1_pre)
  **  ((( &( "fadj" ) )) # Ptr  |-> fadj_pre)
  **  ((( &( "radj" ) )) # Ptr  |-> radj_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (SllPtrArray.full radj_pre n_pre radj_rows_low_level_spec )
  **  (SllPtrArray.full fadj_pre n_pre fadj_rows_low_level_spec )
  **  (IntArray.full vis1_pre n_pre vis1_l_low_level_spec )
  **  (IntArray.full vis2_pre n_pre vis2_l_low_level_spec )
  **  (IntArray.full fin_pre n_pre fin_l_low_level_spec )
  **  (IntArray.full sid_pre n_pre sid_l_low_level_spec )
  **  (IntArray.full timer_p_pre 1 (cons (timer_v_low_level_spec) ((@nil Z))) )
  **  (IntArray.full scc_next_p_pre 1 (cons (scc_next_v_low_level_spec) ((@nil Z))) )
  **  (IntArray.full order_pre n_pre order_l_low_level_spec )
|--
  “ (safeExec (pre_kosaraju (g_low_level_spec) (vis1_l_low_level_spec) (vis2_l_low_level_spec) (fin_l_low_level_spec) (sid_l_low_level_spec) (timer_v_low_level_spec) (scc_next_v_low_level_spec)) kosaraju_finish_monad X_low_level_spec ) ”
.

Definition kosaraju_run_partial_solve_wit_1_aux := 
forall (order_pre: Z) (scc_next_p_pre: Z) (timer_p_pre: Z) (sid_pre: Z) (fin_pre: Z) (vis2_pre: Z) (vis1_pre: Z) (fadj_pre: Z) (radj_pre: Z) (n_pre: Z) (fadj_rows_low_level_spec: (@list (@list Z))) (radj_rows_low_level_spec: (@list (@list Z))) (X_low_level_spec: (unit -> (KSt -> Prop))) (order_l_low_level_spec: (@list Z)) (scc_next_v_low_level_spec: Z) (timer_v_low_level_spec: Z) (sid_l_low_level_spec: (@list Z)) (fin_l_low_level_spec: (@list Z)) (vis2_l_low_level_spec: (@list Z)) (vis1_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (PreH1 : (safeExec (pre_kosaraju (g_low_level_spec) (vis1_l_low_level_spec) (vis2_l_low_level_spec) (fin_l_low_level_spec) (sid_l_low_level_spec) (timer_v_low_level_spec) (scc_next_v_low_level_spec)) kosaraju_monad X_low_level_spec )) (PreH2 : (order_sorted order_l_low_level_spec fin_l_low_level_spec )) (PreH3 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth (j) (order_l_low_level_spec) (0))) /\ ((Znth (j) (order_l_low_level_spec) (0)) < n_pre)))) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre <= INT_MAX)) ,
  (SllPtrArray.full radj_pre n_pre radj_rows_low_level_spec )
  **  (SllPtrArray.full fadj_pre n_pre fadj_rows_low_level_spec )
  **  (IntArray.full vis1_pre n_pre vis1_l_low_level_spec )
  **  (IntArray.full vis2_pre n_pre vis2_l_low_level_spec )
  **  (IntArray.full fin_pre n_pre fin_l_low_level_spec )
  **  (IntArray.full sid_pre n_pre sid_l_low_level_spec )
  **  (IntArray.full timer_p_pre 1 (cons (timer_v_low_level_spec) ((@nil Z))) )
  **  (IntArray.full scc_next_p_pre 1 (cons (scc_next_v_low_level_spec) ((@nil Z))) )
  **  (IntArray.full order_pre n_pre order_l_low_level_spec )
|--
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (safeExec (pre_kosaraju (g_low_level_spec) (vis1_l_low_level_spec) (vis2_l_low_level_spec) (fin_l_low_level_spec) (sid_l_low_level_spec) (timer_v_low_level_spec) (scc_next_v_low_level_spec)) kosaraju_finish_monad X_low_level_spec ) ” 
  &&  “ (safeExec (pre_kosaraju (g_low_level_spec) (vis1_l_low_level_spec) (vis2_l_low_level_spec) (fin_l_low_level_spec) (sid_l_low_level_spec) (timer_v_low_level_spec) (scc_next_v_low_level_spec)) kosaraju_monad X_low_level_spec ) ” 
  &&  “ (order_sorted order_l_low_level_spec fin_l_low_level_spec ) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth (j) (order_l_low_level_spec) (0))) /\ ((Znth (j) (order_l_low_level_spec) (0)) < n_pre))) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ”
  &&  (SllPtrArray.full radj_pre n_pre radj_rows_low_level_spec )
  **  (IntArray.full vis1_pre n_pre vis1_l_low_level_spec )
  **  (IntArray.full fin_pre n_pre fin_l_low_level_spec )
  **  (IntArray.full timer_p_pre 1 (cons (timer_v_low_level_spec) ((@nil Z))) )
  **  (SllPtrArray.full fadj_pre n_pre fadj_rows_low_level_spec )
  **  (IntArray.full vis2_pre n_pre vis2_l_low_level_spec )
  **  (IntArray.full sid_pre n_pre sid_l_low_level_spec )
  **  (IntArray.full scc_next_p_pre 1 (cons (scc_next_v_low_level_spec) ((@nil Z))) )
  **  (IntArray.full order_pre n_pre order_l_low_level_spec )
.

Definition kosaraju_run_partial_solve_wit_1 := kosaraju_run_partial_solve_wit_1_pure -> kosaraju_run_partial_solve_wit_1_aux.

Definition kosaraju_run_partial_solve_wit_2_pure := 
(
forall (order_pre: Z) (scc_next_p_pre: Z) (timer_p_pre: Z) (sid_pre: Z) (fin_pre: Z) (vis2_pre: Z) (vis1_pre: Z) (fadj_pre: Z) (radj_pre: Z) (n_pre: Z) (fadj_rows_low_level_spec: (@list (@list Z))) (radj_rows_low_level_spec: (@list (@list Z))) (X_low_level_spec: (unit -> (KSt -> Prop))) (order_l_low_level_spec: (@list Z)) (scc_next_v_low_level_spec: Z) (timer_v_low_level_spec: Z) (sid_l_low_level_spec: (@list Z)) (fin_l_low_level_spec: (@list Z)) (vis2_l_low_level_spec: (@list Z)) (vis1_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (vis1_l_: (@list Z)) (fin_l_: (@list Z)) (timer_v_: Z) (PreH1 : (safeExec (pre_kosaraju (g_low_level_spec) (vis1_l_) (vis2_l_low_level_spec) (fin_l_) (sid_l_low_level_spec) (timer_v_) (scc_next_v_low_level_spec)) (return (tt)) X_low_level_spec )) (PreH2 : (order_sorted order_l_low_level_spec fin_l_low_level_spec )) (PreH3 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < n_pre)) -> ((0 <= (Znth (j_2) (order_l_low_level_spec) (0))) /\ ((Znth (j_2) (order_l_low_level_spec) (0)) < n_pre)))) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre <= INT_MAX)) ,
  (SllPtrArray.full radj_pre n_pre radj_rows_low_level_spec )
  **  (IntArray.full vis1_pre n_pre vis1_l_ )
  **  (IntArray.full fin_pre n_pre fin_l_ )
  **  (IntArray.full timer_p_pre 1 (cons (timer_v_) ((@nil Z))) )
  **  ((( &( "order" ) )) # Ptr  |-> order_pre)
  **  ((( &( "scc_next_p" ) )) # Ptr  |-> scc_next_p_pre)
  **  ((( &( "timer_p" ) )) # Ptr  |-> timer_p_pre)
  **  ((( &( "sid" ) )) # Ptr  |-> sid_pre)
  **  ((( &( "fin" ) )) # Ptr  |-> fin_pre)
  **  ((( &( "vis2" ) )) # Ptr  |-> vis2_pre)
  **  ((( &( "vis1" ) )) # Ptr  |-> vis1_pre)
  **  ((( &( "fadj" ) )) # Ptr  |-> fadj_pre)
  **  ((( &( "radj" ) )) # Ptr  |-> radj_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (SllPtrArray.full fadj_pre n_pre fadj_rows_low_level_spec )
  **  (IntArray.full vis2_pre n_pre vis2_l_low_level_spec )
  **  (IntArray.full sid_pre n_pre sid_l_low_level_spec )
  **  (IntArray.full scc_next_p_pre 1 (cons (scc_next_v_low_level_spec) ((@nil Z))) )
  **  (IntArray.full order_pre n_pre order_l_low_level_spec )
|--
  “ (order_sorted order_l_low_level_spec fin_l_low_level_spec ) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth (j) (order_l_low_level_spec) (0))) /\ ((Znth (j) (order_l_low_level_spec) (0)) < n_pre))) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (safeExec (pre_kosaraju (g_low_level_spec) (vis1_l_low_level_spec) (vis2_l_low_level_spec) (fin_l_low_level_spec) (sid_l_low_level_spec) (timer_v_low_level_spec) (scc_next_v_low_level_spec)) kosaraju_scc_monad X_low_level_spec ) ” 
  &&  “ (fin_l_ = fin_l_low_level_spec) ”
) \/
(
forall (order_pre: Z) (scc_next_p_pre: Z) (timer_p_pre: Z) (sid_pre: Z) (fin_pre: Z) (vis2_pre: Z) (vis1_pre: Z) (fadj_pre: Z) (radj_pre: Z) (n_pre: Z) (fadj_rows_low_level_spec: (@list (@list Z))) (radj_rows_low_level_spec: (@list (@list Z))) (X_low_level_spec: (unit -> (KSt -> Prop))) (order_l_low_level_spec: (@list Z)) (scc_next_v_low_level_spec: Z) (timer_v_low_level_spec: Z) (sid_l_low_level_spec: (@list Z)) (fin_l_low_level_spec: (@list Z)) (vis2_l_low_level_spec: (@list Z)) (vis1_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (vis1_l_: (@list Z)) (fin_l_: (@list Z)) (timer_v_: Z) (PreH1 : (n_pre <= INT_MAX)) (PreH2 : (n_pre >= INT_MIN)) (PreH3 : (safeExec (pre_kosaraju (g_low_level_spec) (vis1_l_) (vis2_l_low_level_spec) (fin_l_) (sid_l_low_level_spec) (timer_v_) (scc_next_v_low_level_spec)) (return (tt)) X_low_level_spec )) (PreH4 : (order_sorted order_l_low_level_spec fin_l_low_level_spec )) (PreH5 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < n_pre)) -> ((0 <= (Znth (j_2) (order_l_low_level_spec) (0))) /\ ((Znth (j_2) (order_l_low_level_spec) (0)) < n_pre)))) (PreH6 : (0 <= n_pre)) (PreH7 : (n_pre <= INT_MAX)) ,
  (SllPtrArray.full radj_pre n_pre radj_rows_low_level_spec )
  **  (IntArray.full vis1_pre n_pre vis1_l_ )
  **  (IntArray.full fin_pre n_pre fin_l_ )
  **  (IntArray.full timer_p_pre 1 (cons (timer_v_) ((@nil Z))) )
  **  ((( &( "order" ) )) # Ptr  |-> order_pre)
  **  ((( &( "scc_next_p" ) )) # Ptr  |-> scc_next_p_pre)
  **  ((( &( "timer_p" ) )) # Ptr  |-> timer_p_pre)
  **  ((( &( "sid" ) )) # Ptr  |-> sid_pre)
  **  ((( &( "fin" ) )) # Ptr  |-> fin_pre)
  **  ((( &( "vis2" ) )) # Ptr  |-> vis2_pre)
  **  ((( &( "vis1" ) )) # Ptr  |-> vis1_pre)
  **  ((( &( "fadj" ) )) # Ptr  |-> fadj_pre)
  **  ((( &( "radj" ) )) # Ptr  |-> radj_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (SllPtrArray.full fadj_pre n_pre fadj_rows_low_level_spec )
  **  (IntArray.full vis2_pre n_pre vis2_l_low_level_spec )
  **  (IntArray.full sid_pre n_pre sid_l_low_level_spec )
  **  (IntArray.full scc_next_p_pre 1 (cons (scc_next_v_low_level_spec) ((@nil Z))) )
  **  (IntArray.full order_pre n_pre order_l_low_level_spec )
|--
  “ (fin_l_ = fin_l_low_level_spec) ” 
  &&  “ (safeExec (pre_kosaraju (g_low_level_spec) (vis1_l_low_level_spec) (vis2_l_low_level_spec) (fin_l_low_level_spec) (sid_l_low_level_spec) (timer_v_low_level_spec) (scc_next_v_low_level_spec)) kosaraju_scc_monad X_low_level_spec ) ”
).

Definition kosaraju_run_partial_solve_wit_2_pure_split_goal_1 := 
forall (order_pre: Z) (scc_next_p_pre: Z) (timer_p_pre: Z) (sid_pre: Z) (fin_pre: Z) (vis2_pre: Z) (vis1_pre: Z) (fadj_pre: Z) (radj_pre: Z) (n_pre: Z) (fadj_rows_low_level_spec: (@list (@list Z))) (radj_rows_low_level_spec: (@list (@list Z))) (X_low_level_spec: (unit -> (KSt -> Prop))) (order_l_low_level_spec: (@list Z)) (scc_next_v_low_level_spec: Z) (sid_l_low_level_spec: (@list Z)) (fin_l_low_level_spec: (@list Z)) (vis2_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (vis1_l_: (@list Z)) (fin_l_: (@list Z)) (timer_v_: Z) (PreH1 : (n_pre <= INT_MAX)) (PreH2 : (n_pre >= INT_MIN)) (PreH3 : (safeExec (pre_kosaraju (g_low_level_spec) (vis1_l_) (vis2_l_low_level_spec) (fin_l_) (sid_l_low_level_spec) (timer_v_) (scc_next_v_low_level_spec)) (return (tt)) X_low_level_spec )) (PreH4 : (order_sorted order_l_low_level_spec fin_l_low_level_spec )) (PreH5 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < n_pre)) -> ((0 <= (Znth (j_2) (order_l_low_level_spec) (0))) /\ ((Znth (j_2) (order_l_low_level_spec) (0)) < n_pre)))) (PreH6 : (0 <= n_pre)) (PreH7 : (n_pre <= INT_MAX)) ,
  (SllPtrArray.full radj_pre n_pre radj_rows_low_level_spec )
  **  (IntArray.full vis1_pre n_pre vis1_l_ )
  **  (IntArray.full fin_pre n_pre fin_l_ )
  **  (IntArray.full timer_p_pre 1 (cons (timer_v_) ((@nil Z))) )
  **  ((( &( "order" ) )) # Ptr  |-> order_pre)
  **  ((( &( "scc_next_p" ) )) # Ptr  |-> scc_next_p_pre)
  **  ((( &( "timer_p" ) )) # Ptr  |-> timer_p_pre)
  **  ((( &( "sid" ) )) # Ptr  |-> sid_pre)
  **  ((( &( "fin" ) )) # Ptr  |-> fin_pre)
  **  ((( &( "vis2" ) )) # Ptr  |-> vis2_pre)
  **  ((( &( "vis1" ) )) # Ptr  |-> vis1_pre)
  **  ((( &( "fadj" ) )) # Ptr  |-> fadj_pre)
  **  ((( &( "radj" ) )) # Ptr  |-> radj_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (SllPtrArray.full fadj_pre n_pre fadj_rows_low_level_spec )
  **  (IntArray.full vis2_pre n_pre vis2_l_low_level_spec )
  **  (IntArray.full sid_pre n_pre sid_l_low_level_spec )
  **  (IntArray.full scc_next_p_pre 1 (cons (scc_next_v_low_level_spec) ((@nil Z))) )
  **  (IntArray.full order_pre n_pre order_l_low_level_spec )
|--
  “ (fin_l_ = fin_l_low_level_spec) ”
.

Definition kosaraju_run_partial_solve_wit_2_pure_split_goal_2 := 
forall (order_pre: Z) (scc_next_p_pre: Z) (timer_p_pre: Z) (sid_pre: Z) (fin_pre: Z) (vis2_pre: Z) (vis1_pre: Z) (fadj_pre: Z) (radj_pre: Z) (n_pre: Z) (fadj_rows_low_level_spec: (@list (@list Z))) (radj_rows_low_level_spec: (@list (@list Z))) (X_low_level_spec: (unit -> (KSt -> Prop))) (order_l_low_level_spec: (@list Z)) (scc_next_v_low_level_spec: Z) (timer_v_low_level_spec: Z) (sid_l_low_level_spec: (@list Z)) (fin_l_low_level_spec: (@list Z)) (vis2_l_low_level_spec: (@list Z)) (vis1_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (vis1_l_: (@list Z)) (fin_l_: (@list Z)) (timer_v_: Z) (PreH1 : (n_pre <= INT_MAX)) (PreH2 : (n_pre >= INT_MIN)) (PreH3 : (safeExec (pre_kosaraju (g_low_level_spec) (vis1_l_) (vis2_l_low_level_spec) (fin_l_) (sid_l_low_level_spec) (timer_v_) (scc_next_v_low_level_spec)) (return (tt)) X_low_level_spec )) (PreH4 : (order_sorted order_l_low_level_spec fin_l_low_level_spec )) (PreH5 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < n_pre)) -> ((0 <= (Znth (j_2) (order_l_low_level_spec) (0))) /\ ((Znth (j_2) (order_l_low_level_spec) (0)) < n_pre)))) (PreH6 : (0 <= n_pre)) (PreH7 : (n_pre <= INT_MAX)) ,
  (SllPtrArray.full radj_pre n_pre radj_rows_low_level_spec )
  **  (IntArray.full vis1_pre n_pre vis1_l_ )
  **  (IntArray.full fin_pre n_pre fin_l_ )
  **  (IntArray.full timer_p_pre 1 (cons (timer_v_) ((@nil Z))) )
  **  ((( &( "order" ) )) # Ptr  |-> order_pre)
  **  ((( &( "scc_next_p" ) )) # Ptr  |-> scc_next_p_pre)
  **  ((( &( "timer_p" ) )) # Ptr  |-> timer_p_pre)
  **  ((( &( "sid" ) )) # Ptr  |-> sid_pre)
  **  ((( &( "fin" ) )) # Ptr  |-> fin_pre)
  **  ((( &( "vis2" ) )) # Ptr  |-> vis2_pre)
  **  ((( &( "vis1" ) )) # Ptr  |-> vis1_pre)
  **  ((( &( "fadj" ) )) # Ptr  |-> fadj_pre)
  **  ((( &( "radj" ) )) # Ptr  |-> radj_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (SllPtrArray.full fadj_pre n_pre fadj_rows_low_level_spec )
  **  (IntArray.full vis2_pre n_pre vis2_l_low_level_spec )
  **  (IntArray.full sid_pre n_pre sid_l_low_level_spec )
  **  (IntArray.full scc_next_p_pre 1 (cons (scc_next_v_low_level_spec) ((@nil Z))) )
  **  (IntArray.full order_pre n_pre order_l_low_level_spec )
|--
  “ (safeExec (pre_kosaraju (g_low_level_spec) (vis1_l_low_level_spec) (vis2_l_low_level_spec) (fin_l_low_level_spec) (sid_l_low_level_spec) (timer_v_low_level_spec) (scc_next_v_low_level_spec)) kosaraju_scc_monad X_low_level_spec ) ”
.

Definition kosaraju_run_partial_solve_wit_2_aux := 
forall (order_pre: Z) (scc_next_p_pre: Z) (timer_p_pre: Z) (sid_pre: Z) (fin_pre: Z) (vis2_pre: Z) (vis1_pre: Z) (fadj_pre: Z) (radj_pre: Z) (n_pre: Z) (fadj_rows_low_level_spec: (@list (@list Z))) (radj_rows_low_level_spec: (@list (@list Z))) (X_low_level_spec: (unit -> (KSt -> Prop))) (order_l_low_level_spec: (@list Z)) (scc_next_v_low_level_spec: Z) (timer_v_low_level_spec: Z) (sid_l_low_level_spec: (@list Z)) (fin_l_low_level_spec: (@list Z)) (vis2_l_low_level_spec: (@list Z)) (vis1_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (vis1_l_: (@list Z)) (fin_l_: (@list Z)) (timer_v_: Z) (PreH1 : (safeExec (pre_kosaraju (g_low_level_spec) (vis1_l_) (vis2_l_low_level_spec) (fin_l_) (sid_l_low_level_spec) (timer_v_) (scc_next_v_low_level_spec)) (return (tt)) X_low_level_spec )) (PreH2 : (order_sorted order_l_low_level_spec fin_l_low_level_spec )) (PreH3 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < n_pre)) -> ((0 <= (Znth (j_2) (order_l_low_level_spec) (0))) /\ ((Znth (j_2) (order_l_low_level_spec) (0)) < n_pre)))) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre <= INT_MAX)) ,
  (SllPtrArray.full radj_pre n_pre radj_rows_low_level_spec )
  **  (IntArray.full vis1_pre n_pre vis1_l_ )
  **  (IntArray.full fin_pre n_pre fin_l_ )
  **  (IntArray.full timer_p_pre 1 (cons (timer_v_) ((@nil Z))) )
  **  (SllPtrArray.full fadj_pre n_pre fadj_rows_low_level_spec )
  **  (IntArray.full vis2_pre n_pre vis2_l_low_level_spec )
  **  (IntArray.full sid_pre n_pre sid_l_low_level_spec )
  **  (IntArray.full scc_next_p_pre 1 (cons (scc_next_v_low_level_spec) ((@nil Z))) )
  **  (IntArray.full order_pre n_pre order_l_low_level_spec )
|--
  “ (order_sorted order_l_low_level_spec fin_l_low_level_spec ) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth (j) (order_l_low_level_spec) (0))) /\ ((Znth (j) (order_l_low_level_spec) (0)) < n_pre))) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (safeExec (pre_kosaraju (g_low_level_spec) (vis1_l_low_level_spec) (vis2_l_low_level_spec) (fin_l_low_level_spec) (sid_l_low_level_spec) (timer_v_low_level_spec) (scc_next_v_low_level_spec)) kosaraju_scc_monad X_low_level_spec ) ” 
  &&  “ (fin_l_ = fin_l_low_level_spec) ” 
  &&  “ (safeExec (pre_kosaraju (g_low_level_spec) (vis1_l_) (vis2_l_low_level_spec) (fin_l_) (sid_l_low_level_spec) (timer_v_) (scc_next_v_low_level_spec)) (return (tt)) X_low_level_spec ) ” 
  &&  “ (order_sorted order_l_low_level_spec fin_l_low_level_spec ) ” 
  &&  “ forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < n_pre)) -> ((0 <= (Znth (j_2) (order_l_low_level_spec) (0))) /\ ((Znth (j_2) (order_l_low_level_spec) (0)) < n_pre))) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ”
  &&  (SllPtrArray.full fadj_pre n_pre fadj_rows_low_level_spec )
  **  (IntArray.full vis2_pre n_pre vis2_l_low_level_spec )
  **  (IntArray.full sid_pre n_pre sid_l_low_level_spec )
  **  (IntArray.full scc_next_p_pre 1 (cons (scc_next_v_low_level_spec) ((@nil Z))) )
  **  (IntArray.full order_pre n_pre order_l_low_level_spec )
  **  (IntArray.full fin_pre n_pre fin_l_low_level_spec )
  **  (SllPtrArray.full radj_pre n_pre radj_rows_low_level_spec )
  **  (IntArray.full vis1_pre n_pre vis1_l_ )
  **  (IntArray.full timer_p_pre 1 (cons (timer_v_) ((@nil Z))) )
.

Definition kosaraju_run_partial_solve_wit_2 := kosaraju_run_partial_solve_wit_2_pure -> kosaraju_run_partial_solve_wit_2_aux.

Module Type VC_Correct.

Include safeexec_Strategy_Correct.
Include int_array_Strategy_Correct.
Include uint_array_Strategy_Correct.
Include undef_uint_array_Strategy_Correct.
Include array_shape_Strategy_Correct.
Include sll_ptr_array_Strategy_Correct.
Include sll_Strategy_Correct.

Axiom proof_of_kosaraju_num_vertices_return_wit_1 : kosaraju_num_vertices_return_wit_1.
Axiom proof_of_kosaraju_get_visited1_return_wit_1 : kosaraju_get_visited1_return_wit_1.
Axiom proof_of_kosaraju_get_visited1_partial_solve_wit_1 : kosaraju_get_visited1_partial_solve_wit_1.
Axiom proof_of_dfs1_safety_wit_1 : dfs1_safety_wit_1.
Axiom proof_of_dfs1_safety_wit_2 : dfs1_safety_wit_2.
Axiom proof_of_dfs1_safety_wit_3 : dfs1_safety_wit_3.
Axiom proof_of_dfs1_safety_wit_4 : dfs1_safety_wit_4.
Axiom proof_of_dfs1_safety_wit_5 : dfs1_safety_wit_5.
Axiom proof_of_dfs1_safety_wit_6 : dfs1_safety_wit_6.
Axiom proof_of_dfs1_safety_wit_7 : dfs1_safety_wit_7.
Axiom proof_of_dfs1_entail_wit_1 : dfs1_entail_wit_1.
Axiom proof_of_dfs1_entail_wit_2 : dfs1_entail_wit_2.
Axiom proof_of_dfs1_entail_wit_3 : dfs1_entail_wit_3.
Axiom proof_of_dfs1_entail_wit_4_1 : dfs1_entail_wit_4_1.
Axiom proof_of_dfs1_entail_wit_4_2 : dfs1_entail_wit_4_2.
Axiom proof_of_dfs1_entail_wit_5 : dfs1_entail_wit_5.
Axiom proof_of_dfs1_entail_wit_6 : dfs1_entail_wit_6.
Axiom proof_of_dfs1_return_wit_1 : dfs1_return_wit_1.
Axiom proof_of_dfs1_partial_solve_wit_1 : dfs1_partial_solve_wit_1.
Axiom proof_of_dfs1_partial_solve_wit_2 : dfs1_partial_solve_wit_2.
Axiom proof_of_dfs1_partial_solve_wit_3 : dfs1_partial_solve_wit_3.
Axiom proof_of_dfs1_partial_solve_wit_4_pure : dfs1_partial_solve_wit_4_pure.
Axiom proof_of_dfs1_partial_solve_wit_4 : dfs1_partial_solve_wit_4.
Axiom proof_of_dfs1_partial_solve_wit_5 : dfs1_partial_solve_wit_5.
Axiom proof_of_dfs1_partial_solve_wit_6 : dfs1_partial_solve_wit_6.
Axiom proof_of_dfs1_partial_solve_wit_7 : dfs1_partial_solve_wit_7.
Axiom proof_of_dfs2_safety_wit_1 : dfs2_safety_wit_1.
Axiom proof_of_dfs2_safety_wit_2 : dfs2_safety_wit_2.
Axiom proof_of_dfs2_safety_wit_3 : dfs2_safety_wit_3.
Axiom proof_of_dfs2_entail_wit_1 : dfs2_entail_wit_1.
Axiom proof_of_dfs2_entail_wit_2 : dfs2_entail_wit_2.
Axiom proof_of_dfs2_entail_wit_3 : dfs2_entail_wit_3.
Axiom proof_of_dfs2_entail_wit_4_1 : dfs2_entail_wit_4_1.
Axiom proof_of_dfs2_entail_wit_4_2 : dfs2_entail_wit_4_2.
Axiom proof_of_dfs2_entail_wit_5 : dfs2_entail_wit_5.
Axiom proof_of_dfs2_entail_wit_6 : dfs2_entail_wit_6.
Axiom proof_of_dfs2_return_wit_1 : dfs2_return_wit_1.
Axiom proof_of_dfs2_partial_solve_wit_1 : dfs2_partial_solve_wit_1.
Axiom proof_of_dfs2_partial_solve_wit_2 : dfs2_partial_solve_wit_2.
Axiom proof_of_dfs2_partial_solve_wit_3 : dfs2_partial_solve_wit_3.
Axiom proof_of_dfs2_partial_solve_wit_4 : dfs2_partial_solve_wit_4.
Axiom proof_of_dfs2_partial_solve_wit_5 : dfs2_partial_solve_wit_5.
Axiom proof_of_dfs2_partial_solve_wit_6_pure : dfs2_partial_solve_wit_6_pure.
Axiom proof_of_dfs2_partial_solve_wit_6 : dfs2_partial_solve_wit_6.
Axiom proof_of_kosaraju_finish_safety_wit_1 : kosaraju_finish_safety_wit_1.
Axiom proof_of_kosaraju_finish_safety_wit_2 : kosaraju_finish_safety_wit_2.
Axiom proof_of_kosaraju_finish_safety_wit_3 : kosaraju_finish_safety_wit_3.
Axiom proof_of_kosaraju_finish_safety_wit_4 : kosaraju_finish_safety_wit_4.
Axiom proof_of_kosaraju_finish_entail_wit_1 : kosaraju_finish_entail_wit_1.
Axiom proof_of_kosaraju_finish_entail_wit_2 : kosaraju_finish_entail_wit_2.
Axiom proof_of_kosaraju_finish_entail_wit_3_1 : kosaraju_finish_entail_wit_3_1.
Axiom proof_of_kosaraju_finish_entail_wit_3_2 : kosaraju_finish_entail_wit_3_2.
Axiom proof_of_kosaraju_finish_return_wit_1 : kosaraju_finish_return_wit_1.
Axiom proof_of_kosaraju_finish_partial_solve_wit_1 : kosaraju_finish_partial_solve_wit_1.
Axiom proof_of_kosaraju_finish_partial_solve_wit_2_pure : kosaraju_finish_partial_solve_wit_2_pure.
Axiom proof_of_kosaraju_finish_partial_solve_wit_2 : kosaraju_finish_partial_solve_wit_2.
Axiom proof_of_kosaraju_scc_safety_wit_1 : kosaraju_scc_safety_wit_1.
Axiom proof_of_kosaraju_scc_safety_wit_2 : kosaraju_scc_safety_wit_2.
Axiom proof_of_kosaraju_scc_safety_wit_3 : kosaraju_scc_safety_wit_3.
Axiom proof_of_kosaraju_scc_safety_wit_4 : kosaraju_scc_safety_wit_4.
Axiom proof_of_kosaraju_scc_safety_wit_5 : kosaraju_scc_safety_wit_5.
Axiom proof_of_kosaraju_scc_safety_wit_6 : kosaraju_scc_safety_wit_6.
Axiom proof_of_kosaraju_scc_safety_wit_7 : kosaraju_scc_safety_wit_7.
Axiom proof_of_kosaraju_scc_safety_wit_8 : kosaraju_scc_safety_wit_8.
Axiom proof_of_kosaraju_scc_safety_wit_9 : kosaraju_scc_safety_wit_9.
Axiom proof_of_kosaraju_scc_entail_wit_1 : kosaraju_scc_entail_wit_1.
Axiom proof_of_kosaraju_scc_entail_wit_2 : kosaraju_scc_entail_wit_2.
Axiom proof_of_kosaraju_scc_entail_wit_3 : kosaraju_scc_entail_wit_3.
Axiom proof_of_kosaraju_scc_entail_wit_4_1 : kosaraju_scc_entail_wit_4_1.
Axiom proof_of_kosaraju_scc_entail_wit_4_2 : kosaraju_scc_entail_wit_4_2.
Axiom proof_of_kosaraju_scc_return_wit_1 : kosaraju_scc_return_wit_1.
Axiom proof_of_kosaraju_scc_partial_solve_wit_1 : kosaraju_scc_partial_solve_wit_1.
Axiom proof_of_kosaraju_scc_partial_solve_wit_2 : kosaraju_scc_partial_solve_wit_2.
Axiom proof_of_kosaraju_scc_partial_solve_wit_3 : kosaraju_scc_partial_solve_wit_3.
Axiom proof_of_kosaraju_scc_partial_solve_wit_4 : kosaraju_scc_partial_solve_wit_4.
Axiom proof_of_kosaraju_scc_partial_solve_wit_5 : kosaraju_scc_partial_solve_wit_5.
Axiom proof_of_kosaraju_scc_partial_solve_wit_6 : kosaraju_scc_partial_solve_wit_6.
Axiom proof_of_kosaraju_scc_partial_solve_wit_7_pure : kosaraju_scc_partial_solve_wit_7_pure.
Axiom proof_of_kosaraju_scc_partial_solve_wit_7 : kosaraju_scc_partial_solve_wit_7.
Axiom proof_of_kosaraju_run_return_wit_1 : kosaraju_run_return_wit_1.
Axiom proof_of_kosaraju_run_partial_solve_wit_1_pure : kosaraju_run_partial_solve_wit_1_pure.
Axiom proof_of_kosaraju_run_partial_solve_wit_1 : kosaraju_run_partial_solve_wit_1.
Axiom proof_of_kosaraju_run_partial_solve_wit_2_pure : kosaraju_run_partial_solve_wit_2_pure.
Axiom proof_of_kosaraju_run_partial_solve_wit_2 : kosaraju_run_partial_solve_wit_2.

End VC_Correct.
