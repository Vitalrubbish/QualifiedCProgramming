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
From MonadLib.MonadErr Require Export StateRelMonadErr.
Export MonadNotation.
Local Open Scope monad.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap relations.
From FP Require Import PartialOrder_Setoid BourbakiWitt.
Require Import SimpleC.EE.QCP_demos_LLM.kosaraju_rel_lib.
Local Open Scope sac.
From SimpleC.EE.QCP_demos_LLM Require Import safeexecE_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import safeexecE_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import int_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import int_array_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import uint_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import uint_array_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import undef_uint_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import undef_uint_array_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import array_shape_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import array_shape_strategy_proof.

(*----- Function dfs1 -----*)

Definition dfs1_safety_wit_1 := 
forall (timer_p_pre: Z) (fin_pre: Z) (vis1_pre: Z) (radj_row_pre: Z) (radj_col_pre: Z) (n_pre: Z) (u_pre: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (timer_v_low_level_spec: Z) (fin_l_low_level_spec: (@list Z)) (vis1_l_low_level_spec: (@list Z)) (radj_row_l_low_level_spec: (@list Z)) (radj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (PreH1 : (csr_wf1 g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_l_low_level_spec fin_l_low_level_spec )) (PreH2 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH3 : (safeExec (pre_dfs1 (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (vis1_l_low_level_spec) (fin_l_low_level_spec) (timer_v_low_level_spec)) (dfs_finish (g_low_level_spec) (u_pre)) X_low_level_spec )) (PreH4 : (0 <= u_pre)) (PreH5 : (u_pre < n_pre)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : ((Znth (u_pre) (vis1_l_low_level_spec) (0)) = 0)) (PreH8 : (0 <= timer_v_low_level_spec)) (PreH9 : (timer_v_low_level_spec <= (count_nonzero (vis1_l_low_level_spec)))) ,
  ((( &( "timer_p" ) )) # Ptr  |-> timer_p_pre)
  **  ((( &( "fin" ) )) # Ptr  |-> fin_pre)
  **  ((( &( "vis1" ) )) # Ptr  |-> vis1_pre)
  **  ((( &( "radj_row" ) )) # Ptr  |-> radj_row_pre)
  **  ((( &( "radj_col" ) )) # Ptr  |-> radj_col_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "u" ) )) # Int  |-> u_pre)
  **  (IntArray.full radj_col_pre (m_of (radj_row_l_low_level_spec)) radj_col_l_low_level_spec )
  **  (IntArray.full radj_row_pre (n_pre + 1 ) radj_row_l_low_level_spec )
  **  (IntArray.full vis1_pre n_pre vis1_l_low_level_spec )
  **  (IntArray.full fin_pre n_pre fin_l_low_level_spec )
  **  (IntArray.full timer_p_pre 1 (cons (timer_v_low_level_spec) ((@nil Z))) )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition dfs1_safety_wit_2 := 
forall (timer_p_pre: Z) (fin_pre: Z) (vis1_pre: Z) (radj_row_pre: Z) (radj_col_pre: Z) (n_pre: Z) (u_pre: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (timer_v_low_level_spec: Z) (fin_l_low_level_spec: (@list Z)) (vis1_l_low_level_spec: (@list Z)) (radj_row_l_low_level_spec: (@list Z)) (radj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (PreH1 : (csr_wf1 g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_l_low_level_spec fin_l_low_level_spec )) (PreH2 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH3 : (safeExec (pre_dfs1 (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (vis1_l_low_level_spec) (fin_l_low_level_spec) (timer_v_low_level_spec)) (dfs_finish (g_low_level_spec) (u_pre)) X_low_level_spec )) (PreH4 : (0 <= u_pre)) (PreH5 : (u_pre < n_pre)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : ((Znth (u_pre) (vis1_l_low_level_spec) (0)) = 0)) (PreH8 : (0 <= timer_v_low_level_spec)) (PreH9 : (timer_v_low_level_spec <= (count_nonzero (vis1_l_low_level_spec)))) ,
  ((( &( "hi" ) )) # Int  |->_)
  **  (IntArray.full radj_row_pre (n_pre + 1 ) radj_row_l_low_level_spec )
  **  ((( &( "lo" ) )) # Int  |-> (Znth u_pre radj_row_l_low_level_spec 0))
  **  (IntArray.full vis1_pre n_pre (replace_Znth (u_pre) (1) (vis1_l_low_level_spec)) )
  **  ((( &( "timer_p" ) )) # Ptr  |-> timer_p_pre)
  **  ((( &( "fin" ) )) # Ptr  |-> fin_pre)
  **  ((( &( "vis1" ) )) # Ptr  |-> vis1_pre)
  **  ((( &( "radj_row" ) )) # Ptr  |-> radj_row_pre)
  **  ((( &( "radj_col" ) )) # Ptr  |-> radj_col_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "u" ) )) # Int  |-> u_pre)
  **  (IntArray.full radj_col_pre (m_of (radj_row_l_low_level_spec)) radj_col_l_low_level_spec )
  **  (IntArray.full fin_pre n_pre fin_l_low_level_spec )
  **  (IntArray.full timer_p_pre 1 (cons (timer_v_low_level_spec) ((@nil Z))) )
|--
  “ ((u_pre + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (u_pre + 1 )) ”
.

Definition dfs1_safety_wit_3 := 
forall (timer_p_pre: Z) (fin_pre: Z) (vis1_pre: Z) (radj_row_pre: Z) (radj_col_pre: Z) (n_pre: Z) (u_pre: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (timer_v_low_level_spec: Z) (fin_l_low_level_spec: (@list Z)) (vis1_l_low_level_spec: (@list Z)) (radj_row_l_low_level_spec: (@list Z)) (radj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (PreH1 : (csr_wf1 g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_l_low_level_spec fin_l_low_level_spec )) (PreH2 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH3 : (safeExec (pre_dfs1 (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (vis1_l_low_level_spec) (fin_l_low_level_spec) (timer_v_low_level_spec)) (dfs_finish (g_low_level_spec) (u_pre)) X_low_level_spec )) (PreH4 : (0 <= u_pre)) (PreH5 : (u_pre < n_pre)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : ((Znth (u_pre) (vis1_l_low_level_spec) (0)) = 0)) (PreH8 : (0 <= timer_v_low_level_spec)) (PreH9 : (timer_v_low_level_spec <= (count_nonzero (vis1_l_low_level_spec)))) ,
  ((( &( "hi" ) )) # Int  |->_)
  **  (IntArray.full radj_row_pre (n_pre + 1 ) radj_row_l_low_level_spec )
  **  ((( &( "lo" ) )) # Int  |-> (Znth u_pre radj_row_l_low_level_spec 0))
  **  (IntArray.full vis1_pre n_pre (replace_Znth (u_pre) (1) (vis1_l_low_level_spec)) )
  **  ((( &( "timer_p" ) )) # Ptr  |-> timer_p_pre)
  **  ((( &( "fin" ) )) # Ptr  |-> fin_pre)
  **  ((( &( "vis1" ) )) # Ptr  |-> vis1_pre)
  **  ((( &( "radj_row" ) )) # Ptr  |-> radj_row_pre)
  **  ((( &( "radj_col" ) )) # Ptr  |-> radj_col_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "u" ) )) # Int  |-> u_pre)
  **  (IntArray.full radj_col_pre (m_of (radj_row_l_low_level_spec)) radj_col_l_low_level_spec )
  **  (IntArray.full fin_pre n_pre fin_l_low_level_spec )
  **  (IntArray.full timer_p_pre 1 (cons (timer_v_low_level_spec) ((@nil Z))) )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition dfs1_safety_wit_4 := 
forall (timer_p_pre: Z) (fin_pre: Z) (vis1_pre: Z) (radj_row_pre: Z) (radj_col_pre: Z) (n_pre: Z) (u_pre: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (timer_v_low_level_spec: Z) (vis1_l_low_level_spec: (@list Z)) (radj_row_l_low_level_spec: (@list Z)) (radj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (vis1_m: (@list Z)) (fin_m: (@list Z)) (timer_m: Z) (i: Z) (lo: Z) (hi: Z) (v: Z) (PreH1 : (csr_wf1 g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_m fin_m )) (PreH2 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH3 : (safeExec (pre_dfs1 (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (vis1_m) (fin_m) (timer_m)) (dfs_finish_from (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (u_pre) (i)) X_low_level_spec )) (PreH4 : (lo = (csr_lo (u_pre) (radj_row_l_low_level_spec)))) (PreH5 : (hi = (csr_hi (u_pre) (radj_row_l_low_level_spec)))) (PreH6 : (0 <= lo)) (PreH7 : (lo <= i)) (PreH8 : (i < hi)) (PreH9 : (hi <= (m_of (radj_row_l_low_level_spec)))) (PreH10 : (0 <= u_pre)) (PreH11 : (u_pre < n_pre)) (PreH12 : (n_pre <= INT_MAX)) (PreH13 : (0 <= timer_m)) (PreH14 : (timer_m < (count_nonzero (vis1_m)))) (PreH15 : (((count_nonzero (vis1_m)) - timer_m ) = (((count_nonzero (vis1_l_low_level_spec)) - timer_v_low_level_spec ) + 1 ))) (PreH16 : (0 <= v)) (PreH17 : (v < n_pre)) (PreH18 : (v = (Znth (i) (radj_col_l_low_level_spec) (0)))) ,
  (IntArray.full vis1_pre n_pre vis1_m )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "u" ) )) # Int  |-> u_pre)
  **  ((( &( "radj_col" ) )) # Ptr  |-> radj_col_pre)
  **  ((( &( "radj_row" ) )) # Ptr  |-> radj_row_pre)
  **  ((( &( "vis1" ) )) # Ptr  |-> vis1_pre)
  **  ((( &( "fin" ) )) # Ptr  |-> fin_pre)
  **  ((( &( "timer_p" ) )) # Ptr  |-> timer_p_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  (IntArray.full radj_col_pre (m_of (radj_row_l_low_level_spec)) radj_col_l_low_level_spec )
  **  (IntArray.full radj_row_pre (n_pre + 1 ) radj_row_l_low_level_spec )
  **  (IntArray.full fin_pre n_pre fin_m )
  **  (IntArray.full timer_p_pre 1 (cons (timer_m) ((@nil Z))) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition dfs1_safety_wit_5 := 
forall (timer_p_pre: Z) (fin_pre: Z) (vis1_pre: Z) (radj_row_pre: Z) (radj_col_pre: Z) (n_pre: Z) (u_pre: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (timer_v_low_level_spec: Z) (vis1_l_low_level_spec: (@list Z)) (radj_row_l_low_level_spec: (@list Z)) (radj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (vis1_m: (@list Z)) (fin_m: (@list Z)) (timer_m: Z) (i: Z) (lo: Z) (hi: Z) (v: Z) (timer_v_: Z) (vis1_l_: (@list Z)) (fin_l_: (@list Z)) (PreH1 : (csr_wf1 g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_l_ fin_l_ )) (PreH2 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH3 : (safeExec (pre_dfs1 (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (vis1_l_) (fin_l_) (timer_v_)) (applyf ((dfs_finish_fromK (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (u_pre) ((i + 1 )))) (tt)) X_low_level_spec )) (PreH4 : (0 <= timer_v_)) (PreH5 : (((count_nonzero (vis1_l_)) - timer_v_ ) = ((count_nonzero (vis1_m)) - timer_m ))) (PreH6 : ((Znth v vis1_m 0) = 0)) (PreH7 : (csr_wf1 g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_m fin_m )) (PreH8 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH9 : (lo = (csr_lo (u_pre) (radj_row_l_low_level_spec)))) (PreH10 : (hi = (csr_hi (u_pre) (radj_row_l_low_level_spec)))) (PreH11 : (0 <= lo)) (PreH12 : (lo <= i)) (PreH13 : (i < hi)) (PreH14 : (hi <= (m_of (radj_row_l_low_level_spec)))) (PreH15 : (0 <= u_pre)) (PreH16 : (u_pre < n_pre)) (PreH17 : (n_pre <= INT_MAX)) (PreH18 : (0 <= timer_m)) (PreH19 : (timer_m < (count_nonzero (vis1_m)))) (PreH20 : (((count_nonzero (vis1_m)) - timer_m ) = (((count_nonzero (vis1_l_low_level_spec)) - timer_v_low_level_spec ) + 1 ))) (PreH21 : (0 <= v)) (PreH22 : (v < n_pre)) (PreH23 : (v = (Znth (i) (radj_col_l_low_level_spec) (0)))) ,
  (IntArray.full radj_col_pre (m_of (radj_row_l_low_level_spec)) radj_col_l_low_level_spec )
  **  (IntArray.full radj_row_pre (n_pre + 1 ) radj_row_l_low_level_spec )
  **  (IntArray.full vis1_pre n_pre vis1_l_ )
  **  (IntArray.full fin_pre n_pre fin_l_ )
  **  (IntArray.full timer_p_pre 1 (cons (timer_v_) ((@nil Z))) )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "u" ) )) # Int  |-> u_pre)
  **  ((( &( "radj_col" ) )) # Ptr  |-> radj_col_pre)
  **  ((( &( "radj_row" ) )) # Ptr  |-> radj_row_pre)
  **  ((( &( "vis1" ) )) # Ptr  |-> vis1_pre)
  **  ((( &( "fin" ) )) # Ptr  |-> fin_pre)
  **  ((( &( "timer_p" ) )) # Ptr  |-> timer_p_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "v" ) )) # Int  |-> v)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition dfs1_safety_wit_6 := 
forall (timer_p_pre: Z) (fin_pre: Z) (vis1_pre: Z) (radj_row_pre: Z) (radj_col_pre: Z) (n_pre: Z) (u_pre: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (timer_v_low_level_spec: Z) (vis1_l_low_level_spec: (@list Z)) (radj_row_l_low_level_spec: (@list Z)) (radj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (vis1_m: (@list Z)) (fin_m: (@list Z)) (timer_m: Z) (i: Z) (lo: Z) (hi: Z) (v: Z) (timer_v_: Z) (vis1_l_: (@list Z)) (fin_l_: (@list Z)) (PreH1 : (csr_wf1 g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_l_ fin_l_ )) (PreH2 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH3 : (safeExec (pre_dfs1 (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (vis1_l_) (fin_l_) (timer_v_)) (applyf ((dfs_finish_fromK (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (u_pre) ((i + 1 )))) (tt)) X_low_level_spec )) (PreH4 : (0 <= timer_v_)) (PreH5 : (((count_nonzero (vis1_l_)) - timer_v_ ) = ((count_nonzero (vis1_m)) - timer_m ))) (PreH6 : ((Znth v vis1_m 0) = 0)) (PreH7 : (csr_wf1 g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_m fin_m )) (PreH8 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH9 : (lo = (csr_lo (u_pre) (radj_row_l_low_level_spec)))) (PreH10 : (hi = (csr_hi (u_pre) (radj_row_l_low_level_spec)))) (PreH11 : (0 <= lo)) (PreH12 : (lo <= i)) (PreH13 : (i < hi)) (PreH14 : (hi <= (m_of (radj_row_l_low_level_spec)))) (PreH15 : (0 <= u_pre)) (PreH16 : (u_pre < n_pre)) (PreH17 : (n_pre <= INT_MAX)) (PreH18 : (0 <= timer_m)) (PreH19 : (timer_m < (count_nonzero (vis1_m)))) (PreH20 : (((count_nonzero (vis1_m)) - timer_m ) = (((count_nonzero (vis1_l_low_level_spec)) - timer_v_low_level_spec ) + 1 ))) (PreH21 : (0 <= v)) (PreH22 : (v < n_pre)) (PreH23 : (v = (Znth (i) (radj_col_l_low_level_spec) (0)))) ,
  (IntArray.full radj_col_pre (m_of (radj_row_l_low_level_spec)) radj_col_l_low_level_spec )
  **  (IntArray.full radj_row_pre (n_pre + 1 ) radj_row_l_low_level_spec )
  **  (IntArray.full vis1_pre n_pre vis1_l_ )
  **  (IntArray.full fin_pre n_pre fin_l_ )
  **  (IntArray.full timer_p_pre 1 (cons (timer_v_) ((@nil Z))) )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "u" ) )) # Int  |-> u_pre)
  **  ((( &( "radj_col" ) )) # Ptr  |-> radj_col_pre)
  **  ((( &( "radj_row" ) )) # Ptr  |-> radj_row_pre)
  **  ((( &( "vis1" ) )) # Ptr  |-> vis1_pre)
  **  ((( &( "fin" ) )) # Ptr  |-> fin_pre)
  **  ((( &( "timer_p" ) )) # Ptr  |-> timer_p_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "v" ) )) # Int  |-> v)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition dfs1_safety_wit_7 := 
forall (timer_p_pre: Z) (fin_pre: Z) (vis1_pre: Z) (radj_row_pre: Z) (radj_col_pre: Z) (n_pre: Z) (u_pre: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (timer_v_low_level_spec: Z) (vis1_l_low_level_spec: (@list Z)) (radj_row_l_low_level_spec: (@list Z)) (radj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (vis1_m: (@list Z)) (fin_m: (@list Z)) (timer_m: Z) (i: Z) (lo: Z) (hi: Z) (v: Z) (PreH1 : ((Znth v vis1_m 0) <> 0)) (PreH2 : (csr_wf1 g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_m fin_m )) (PreH3 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH4 : (safeExec (pre_dfs1 (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (vis1_m) (fin_m) (timer_m)) (dfs_finish_from (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (u_pre) (i)) X_low_level_spec )) (PreH5 : (lo = (csr_lo (u_pre) (radj_row_l_low_level_spec)))) (PreH6 : (hi = (csr_hi (u_pre) (radj_row_l_low_level_spec)))) (PreH7 : (0 <= lo)) (PreH8 : (lo <= i)) (PreH9 : (i < hi)) (PreH10 : (hi <= (m_of (radj_row_l_low_level_spec)))) (PreH11 : (0 <= u_pre)) (PreH12 : (u_pre < n_pre)) (PreH13 : (n_pre <= INT_MAX)) (PreH14 : (0 <= timer_m)) (PreH15 : (timer_m < (count_nonzero (vis1_m)))) (PreH16 : (((count_nonzero (vis1_m)) - timer_m ) = (((count_nonzero (vis1_l_low_level_spec)) - timer_v_low_level_spec ) + 1 ))) (PreH17 : (0 <= v)) (PreH18 : (v < n_pre)) (PreH19 : (v = (Znth (i) (radj_col_l_low_level_spec) (0)))) ,
  (IntArray.full vis1_pre n_pre vis1_m )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "u" ) )) # Int  |-> u_pre)
  **  ((( &( "radj_col" ) )) # Ptr  |-> radj_col_pre)
  **  ((( &( "radj_row" ) )) # Ptr  |-> radj_row_pre)
  **  ((( &( "vis1" ) )) # Ptr  |-> vis1_pre)
  **  ((( &( "fin" ) )) # Ptr  |-> fin_pre)
  **  ((( &( "timer_p" ) )) # Ptr  |-> timer_p_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  (IntArray.full radj_col_pre (m_of (radj_row_l_low_level_spec)) radj_col_l_low_level_spec )
  **  (IntArray.full radj_row_pre (n_pre + 1 ) radj_row_l_low_level_spec )
  **  (IntArray.full fin_pre n_pre fin_m )
  **  (IntArray.full timer_p_pre 1 (cons (timer_m) ((@nil Z))) )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition dfs1_safety_wit_8 := 
forall (timer_p_pre: Z) (fin_pre: Z) (vis1_pre: Z) (radj_row_pre: Z) (radj_col_pre: Z) (n_pre: Z) (u_pre: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (timer_v_low_level_spec: Z) (vis1_l_low_level_spec: (@list Z)) (radj_row_l_low_level_spec: (@list Z)) (radj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (vis1_m: (@list Z)) (fin_m: (@list Z)) (timer_m: Z) (i: Z) (lo: Z) (hi: Z) (v: Z) (PreH1 : ((Znth v vis1_m 0) <> 0)) (PreH2 : (csr_wf1 g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_m fin_m )) (PreH3 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH4 : (safeExec (pre_dfs1 (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (vis1_m) (fin_m) (timer_m)) (dfs_finish_from (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (u_pre) (i)) X_low_level_spec )) (PreH5 : (lo = (csr_lo (u_pre) (radj_row_l_low_level_spec)))) (PreH6 : (hi = (csr_hi (u_pre) (radj_row_l_low_level_spec)))) (PreH7 : (0 <= lo)) (PreH8 : (lo <= i)) (PreH9 : (i < hi)) (PreH10 : (hi <= (m_of (radj_row_l_low_level_spec)))) (PreH11 : (0 <= u_pre)) (PreH12 : (u_pre < n_pre)) (PreH13 : (n_pre <= INT_MAX)) (PreH14 : (0 <= timer_m)) (PreH15 : (timer_m < (count_nonzero (vis1_m)))) (PreH16 : (((count_nonzero (vis1_m)) - timer_m ) = (((count_nonzero (vis1_l_low_level_spec)) - timer_v_low_level_spec ) + 1 ))) (PreH17 : (0 <= v)) (PreH18 : (v < n_pre)) (PreH19 : (v = (Znth (i) (radj_col_l_low_level_spec) (0)))) ,
  (IntArray.full vis1_pre n_pre vis1_m )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "u" ) )) # Int  |-> u_pre)
  **  ((( &( "radj_col" ) )) # Ptr  |-> radj_col_pre)
  **  ((( &( "radj_row" ) )) # Ptr  |-> radj_row_pre)
  **  ((( &( "vis1" ) )) # Ptr  |-> vis1_pre)
  **  ((( &( "fin" ) )) # Ptr  |-> fin_pre)
  **  ((( &( "timer_p" ) )) # Ptr  |-> timer_p_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  (IntArray.full radj_col_pre (m_of (radj_row_l_low_level_spec)) radj_col_l_low_level_spec )
  **  (IntArray.full radj_row_pre (n_pre + 1 ) radj_row_l_low_level_spec )
  **  (IntArray.full fin_pre n_pre fin_m )
  **  (IntArray.full timer_p_pre 1 (cons (timer_m) ((@nil Z))) )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition dfs1_safety_wit_9 := 
forall (timer_p_pre: Z) (fin_pre: Z) (vis1_pre: Z) (radj_row_pre: Z) (radj_col_pre: Z) (n_pre: Z) (u_pre: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (timer_v_low_level_spec: Z) (vis1_l_low_level_spec: (@list Z)) (radj_row_l_low_level_spec: (@list Z)) (radj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (hi: Z) (lo: Z) (timer_m: Z) (i: Z) (vis1_m: (@list Z)) (fin_m: (@list Z)) (PreH1 : (i >= hi)) (PreH2 : (csr_wf1 g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_m fin_m )) (PreH3 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH4 : (safeExec (pre_dfs1 (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (vis1_m) (fin_m) (timer_m)) (dfs_finish_from (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (u_pre) (i)) X_low_level_spec )) (PreH5 : (lo = (csr_lo (u_pre) (radj_row_l_low_level_spec)))) (PreH6 : (hi = (csr_hi (u_pre) (radj_row_l_low_level_spec)))) (PreH7 : (0 <= lo)) (PreH8 : (lo <= i)) (PreH9 : (i <= hi)) (PreH10 : (hi <= (m_of (radj_row_l_low_level_spec)))) (PreH11 : (0 <= u_pre)) (PreH12 : (u_pre < n_pre)) (PreH13 : (n_pre <= INT_MAX)) (PreH14 : (0 <= timer_m)) (PreH15 : (timer_m < (count_nonzero (vis1_m)))) (PreH16 : (((count_nonzero (vis1_m)) - timer_m ) = (((count_nonzero (vis1_l_low_level_spec)) - timer_v_low_level_spec ) + 1 ))) ,
  ((( &( "t0" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "u" ) )) # Int  |-> u_pre)
  **  ((( &( "radj_col" ) )) # Ptr  |-> radj_col_pre)
  **  ((( &( "radj_row" ) )) # Ptr  |-> radj_row_pre)
  **  ((( &( "vis1" ) )) # Ptr  |-> vis1_pre)
  **  ((( &( "fin" ) )) # Ptr  |-> fin_pre)
  **  ((( &( "timer_p" ) )) # Ptr  |-> timer_p_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  (IntArray.full radj_col_pre (m_of (radj_row_l_low_level_spec)) radj_col_l_low_level_spec )
  **  (IntArray.full radj_row_pre (n_pre + 1 ) radj_row_l_low_level_spec )
  **  (IntArray.full vis1_pre n_pre vis1_m )
  **  (IntArray.full fin_pre n_pre fin_m )
  **  (IntArray.full timer_p_pre 1 (cons (timer_m) ((@nil Z))) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition dfs1_safety_wit_10 := 
forall (timer_p_pre: Z) (fin_pre: Z) (vis1_pre: Z) (radj_row_pre: Z) (radj_col_pre: Z) (n_pre: Z) (u_pre: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (timer_v_low_level_spec: Z) (vis1_l_low_level_spec: (@list Z)) (radj_row_l_low_level_spec: (@list Z)) (radj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (hi: Z) (lo: Z) (timer_m: Z) (i: Z) (vis1_m: (@list Z)) (fin_m: (@list Z)) (PreH1 : (i >= hi)) (PreH2 : (csr_wf1 g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_m fin_m )) (PreH3 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH4 : (safeExec (pre_dfs1 (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (vis1_m) (fin_m) (timer_m)) (dfs_finish_from (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (u_pre) (i)) X_low_level_spec )) (PreH5 : (lo = (csr_lo (u_pre) (radj_row_l_low_level_spec)))) (PreH6 : (hi = (csr_hi (u_pre) (radj_row_l_low_level_spec)))) (PreH7 : (0 <= lo)) (PreH8 : (lo <= i)) (PreH9 : (i <= hi)) (PreH10 : (hi <= (m_of (radj_row_l_low_level_spec)))) (PreH11 : (0 <= u_pre)) (PreH12 : (u_pre < n_pre)) (PreH13 : (n_pre <= INT_MAX)) (PreH14 : (0 <= timer_m)) (PreH15 : (timer_m < (count_nonzero (vis1_m)))) (PreH16 : (((count_nonzero (vis1_m)) - timer_m ) = (((count_nonzero (vis1_l_low_level_spec)) - timer_v_low_level_spec ) + 1 ))) ,
  (IntArray.full fin_pre n_pre (replace_Znth (u_pre) ((Znth 0 (cons (timer_m) ((@nil Z))) 0)) (fin_m)) )
  **  (IntArray.full timer_p_pre 1 (cons (timer_m) ((@nil Z))) )
  **  ((( &( "t0" ) )) # Int  |-> (Znth 0 (cons (timer_m) ((@nil Z))) 0))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "u" ) )) # Int  |-> u_pre)
  **  ((( &( "radj_col" ) )) # Ptr  |-> radj_col_pre)
  **  ((( &( "radj_row" ) )) # Ptr  |-> radj_row_pre)
  **  ((( &( "vis1" ) )) # Ptr  |-> vis1_pre)
  **  ((( &( "fin" ) )) # Ptr  |-> fin_pre)
  **  ((( &( "timer_p" ) )) # Ptr  |-> timer_p_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  (IntArray.full radj_col_pre (m_of (radj_row_l_low_level_spec)) radj_col_l_low_level_spec )
  **  (IntArray.full radj_row_pre (n_pre + 1 ) radj_row_l_low_level_spec )
  **  (IntArray.full vis1_pre n_pre vis1_m )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition dfs1_safety_wit_11 := 
(
forall (timer_p_pre: Z) (fin_pre: Z) (vis1_pre: Z) (radj_row_pre: Z) (radj_col_pre: Z) (n_pre: Z) (u_pre: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (timer_v_low_level_spec: Z) (vis1_l_low_level_spec: (@list Z)) (radj_row_l_low_level_spec: (@list Z)) (radj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (hi: Z) (lo: Z) (timer_m: Z) (i: Z) (vis1_m: (@list Z)) (fin_m: (@list Z)) (PreH1 : (i >= hi)) (PreH2 : (csr_wf1 g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_m fin_m )) (PreH3 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH4 : (safeExec (pre_dfs1 (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (vis1_m) (fin_m) (timer_m)) (dfs_finish_from (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (u_pre) (i)) X_low_level_spec )) (PreH5 : (lo = (csr_lo (u_pre) (radj_row_l_low_level_spec)))) (PreH6 : (hi = (csr_hi (u_pre) (radj_row_l_low_level_spec)))) (PreH7 : (0 <= lo)) (PreH8 : (lo <= i)) (PreH9 : (i <= hi)) (PreH10 : (hi <= (m_of (radj_row_l_low_level_spec)))) (PreH11 : (0 <= u_pre)) (PreH12 : (u_pre < n_pre)) (PreH13 : (n_pre <= INT_MAX)) (PreH14 : (0 <= timer_m)) (PreH15 : (timer_m < (count_nonzero (vis1_m)))) (PreH16 : (((count_nonzero (vis1_m)) - timer_m ) = (((count_nonzero (vis1_l_low_level_spec)) - timer_v_low_level_spec ) + 1 ))) ,
  (IntArray.full fin_pre n_pre (replace_Znth (u_pre) ((Znth 0 (cons (timer_m) ((@nil Z))) 0)) (fin_m)) )
  **  (IntArray.full timer_p_pre 1 (cons (timer_m) ((@nil Z))) )
  **  ((( &( "t0" ) )) # Int  |-> (Znth 0 (cons (timer_m) ((@nil Z))) 0))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "u" ) )) # Int  |-> u_pre)
  **  ((( &( "radj_col" ) )) # Ptr  |-> radj_col_pre)
  **  ((( &( "radj_row" ) )) # Ptr  |-> radj_row_pre)
  **  ((( &( "vis1" ) )) # Ptr  |-> vis1_pre)
  **  ((( &( "fin" ) )) # Ptr  |-> fin_pre)
  **  ((( &( "timer_p" ) )) # Ptr  |-> timer_p_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  (IntArray.full radj_col_pre (m_of (radj_row_l_low_level_spec)) radj_col_l_low_level_spec )
  **  (IntArray.full radj_row_pre (n_pre + 1 ) radj_row_l_low_level_spec )
  **  (IntArray.full vis1_pre n_pre vis1_m )
|--
  “ (((Znth 0 (cons (timer_m) ((@nil Z))) 0) + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth 0 (cons (timer_m) ((@nil Z))) 0) + 1 )) ”
) \/
(
forall (timer_p_pre: Z) (fin_pre: Z) (vis1_pre: Z) (radj_row_pre: Z) (radj_col_pre: Z) (n_pre: Z) (u_pre: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (timer_v_low_level_spec: Z) (vis1_l_low_level_spec: (@list Z)) (radj_row_l_low_level_spec: (@list Z)) (radj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (hi: Z) (lo: Z) (timer_m: Z) (i: Z) (vis1_m: (@list Z)) (fin_m: (@list Z)) (PreH1 : (i >= hi)) (PreH2 : (csr_wf1 g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_m fin_m )) (PreH3 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH4 : (safeExec (pre_dfs1 (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (vis1_m) (fin_m) (timer_m)) (dfs_finish_from (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (u_pre) (i)) X_low_level_spec )) (PreH5 : (lo = (csr_lo (u_pre) (radj_row_l_low_level_spec)))) (PreH6 : (hi = (csr_hi (u_pre) (radj_row_l_low_level_spec)))) (PreH7 : (0 <= lo)) (PreH8 : (lo <= i)) (PreH9 : (i <= hi)) (PreH10 : (hi <= (m_of (radj_row_l_low_level_spec)))) (PreH11 : (0 <= u_pre)) (PreH12 : (u_pre < n_pre)) (PreH13 : (n_pre <= INT_MAX)) (PreH14 : (0 <= timer_m)) (PreH15 : (timer_m < (count_nonzero (vis1_m)))) (PreH16 : (((count_nonzero (vis1_m)) - timer_m ) = (((count_nonzero (vis1_l_low_level_spec)) - timer_v_low_level_spec ) + 1 ))) ,
  (IntArray.full fin_pre n_pre (replace_Znth (u_pre) ((Znth 0 (cons (timer_m) ((@nil Z))) 0)) (fin_m)) )
  **  (IntArray.full timer_p_pre 1 (cons (timer_m) ((@nil Z))) )
  **  ((( &( "t0" ) )) # Int  |-> (Znth 0 (cons (timer_m) ((@nil Z))) 0))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "u" ) )) # Int  |-> u_pre)
  **  ((( &( "radj_col" ) )) # Ptr  |-> radj_col_pre)
  **  ((( &( "radj_row" ) )) # Ptr  |-> radj_row_pre)
  **  ((( &( "vis1" ) )) # Ptr  |-> vis1_pre)
  **  ((( &( "fin" ) )) # Ptr  |-> fin_pre)
  **  ((( &( "timer_p" ) )) # Ptr  |-> timer_p_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  (IntArray.full radj_col_pre (m_of (radj_row_l_low_level_spec)) radj_col_l_low_level_spec )
  **  (IntArray.full radj_row_pre (n_pre + 1 ) radj_row_l_low_level_spec )
  **  (IntArray.full vis1_pre n_pre vis1_m )
|--
  “ (((Znth 0 (cons (timer_m) ((@nil Z))) 0) + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth 0 (cons (timer_m) ((@nil Z))) 0) + 1 )) ”
).

Definition dfs1_safety_wit_11_split_goal_1 := 
forall (timer_p_pre: Z) (fin_pre: Z) (vis1_pre: Z) (radj_row_pre: Z) (radj_col_pre: Z) (n_pre: Z) (u_pre: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (timer_v_low_level_spec: Z) (vis1_l_low_level_spec: (@list Z)) (radj_row_l_low_level_spec: (@list Z)) (radj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (hi: Z) (lo: Z) (timer_m: Z) (i: Z) (vis1_m: (@list Z)) (fin_m: (@list Z)) (PreH1 : (i >= hi)) (PreH2 : (csr_wf1 g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_m fin_m )) (PreH3 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH4 : (safeExec (pre_dfs1 (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (vis1_m) (fin_m) (timer_m)) (dfs_finish_from (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (u_pre) (i)) X_low_level_spec )) (PreH5 : (lo = (csr_lo (u_pre) (radj_row_l_low_level_spec)))) (PreH6 : (hi = (csr_hi (u_pre) (radj_row_l_low_level_spec)))) (PreH7 : (0 <= lo)) (PreH8 : (lo <= i)) (PreH9 : (i <= hi)) (PreH10 : (hi <= (m_of (radj_row_l_low_level_spec)))) (PreH11 : (0 <= u_pre)) (PreH12 : (u_pre < n_pre)) (PreH13 : (n_pre <= INT_MAX)) (PreH14 : (0 <= timer_m)) (PreH15 : (timer_m < (count_nonzero (vis1_m)))) (PreH16 : (((count_nonzero (vis1_m)) - timer_m ) = (((count_nonzero (vis1_l_low_level_spec)) - timer_v_low_level_spec ) + 1 ))) ,
  (IntArray.full fin_pre n_pre (replace_Znth (u_pre) ((Znth 0 (cons (timer_m) ((@nil Z))) 0)) (fin_m)) )
  **  (IntArray.full timer_p_pre 1 (cons (timer_m) ((@nil Z))) )
  **  ((( &( "t0" ) )) # Int  |-> (Znth 0 (cons (timer_m) ((@nil Z))) 0))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "u" ) )) # Int  |-> u_pre)
  **  ((( &( "radj_col" ) )) # Ptr  |-> radj_col_pre)
  **  ((( &( "radj_row" ) )) # Ptr  |-> radj_row_pre)
  **  ((( &( "vis1" ) )) # Ptr  |-> vis1_pre)
  **  ((( &( "fin" ) )) # Ptr  |-> fin_pre)
  **  ((( &( "timer_p" ) )) # Ptr  |-> timer_p_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  (IntArray.full radj_col_pre (m_of (radj_row_l_low_level_spec)) radj_col_l_low_level_spec )
  **  (IntArray.full radj_row_pre (n_pre + 1 ) radj_row_l_low_level_spec )
  **  (IntArray.full vis1_pre n_pre vis1_m )
|--
  “ (((Znth 0 (cons (timer_m) ((@nil Z))) 0) + 1 ) <= INT_MAX) ”
.

Definition dfs1_safety_wit_11_split_goal_2 := 
forall (timer_p_pre: Z) (fin_pre: Z) (vis1_pre: Z) (radj_row_pre: Z) (radj_col_pre: Z) (n_pre: Z) (u_pre: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (timer_v_low_level_spec: Z) (vis1_l_low_level_spec: (@list Z)) (radj_row_l_low_level_spec: (@list Z)) (radj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (hi: Z) (lo: Z) (timer_m: Z) (i: Z) (vis1_m: (@list Z)) (fin_m: (@list Z)) (PreH1 : (i >= hi)) (PreH2 : (csr_wf1 g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_m fin_m )) (PreH3 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH4 : (safeExec (pre_dfs1 (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (vis1_m) (fin_m) (timer_m)) (dfs_finish_from (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (u_pre) (i)) X_low_level_spec )) (PreH5 : (lo = (csr_lo (u_pre) (radj_row_l_low_level_spec)))) (PreH6 : (hi = (csr_hi (u_pre) (radj_row_l_low_level_spec)))) (PreH7 : (0 <= lo)) (PreH8 : (lo <= i)) (PreH9 : (i <= hi)) (PreH10 : (hi <= (m_of (radj_row_l_low_level_spec)))) (PreH11 : (0 <= u_pre)) (PreH12 : (u_pre < n_pre)) (PreH13 : (n_pre <= INT_MAX)) (PreH14 : (0 <= timer_m)) (PreH15 : (timer_m < (count_nonzero (vis1_m)))) (PreH16 : (((count_nonzero (vis1_m)) - timer_m ) = (((count_nonzero (vis1_l_low_level_spec)) - timer_v_low_level_spec ) + 1 ))) ,
  (IntArray.full fin_pre n_pre (replace_Znth (u_pre) ((Znth 0 (cons (timer_m) ((@nil Z))) 0)) (fin_m)) )
  **  (IntArray.full timer_p_pre 1 (cons (timer_m) ((@nil Z))) )
  **  ((( &( "t0" ) )) # Int  |-> (Znth 0 (cons (timer_m) ((@nil Z))) 0))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "u" ) )) # Int  |-> u_pre)
  **  ((( &( "radj_col" ) )) # Ptr  |-> radj_col_pre)
  **  ((( &( "radj_row" ) )) # Ptr  |-> radj_row_pre)
  **  ((( &( "vis1" ) )) # Ptr  |-> vis1_pre)
  **  ((( &( "fin" ) )) # Ptr  |-> fin_pre)
  **  ((( &( "timer_p" ) )) # Ptr  |-> timer_p_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  (IntArray.full radj_col_pre (m_of (radj_row_l_low_level_spec)) radj_col_l_low_level_spec )
  **  (IntArray.full radj_row_pre (n_pre + 1 ) radj_row_l_low_level_spec )
  **  (IntArray.full vis1_pre n_pre vis1_m )
|--
  “ ((INT_MIN) <= ((Znth 0 (cons (timer_m) ((@nil Z))) 0) + 1 )) ”
.

Definition dfs1_safety_wit_12 := 
forall (timer_p_pre: Z) (fin_pre: Z) (vis1_pre: Z) (radj_row_pre: Z) (radj_col_pre: Z) (n_pre: Z) (u_pre: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (timer_v_low_level_spec: Z) (vis1_l_low_level_spec: (@list Z)) (radj_row_l_low_level_spec: (@list Z)) (radj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (hi: Z) (lo: Z) (timer_m: Z) (i: Z) (vis1_m: (@list Z)) (fin_m: (@list Z)) (PreH1 : (i >= hi)) (PreH2 : (csr_wf1 g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_m fin_m )) (PreH3 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH4 : (safeExec (pre_dfs1 (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (vis1_m) (fin_m) (timer_m)) (dfs_finish_from (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (u_pre) (i)) X_low_level_spec )) (PreH5 : (lo = (csr_lo (u_pre) (radj_row_l_low_level_spec)))) (PreH6 : (hi = (csr_hi (u_pre) (radj_row_l_low_level_spec)))) (PreH7 : (0 <= lo)) (PreH8 : (lo <= i)) (PreH9 : (i <= hi)) (PreH10 : (hi <= (m_of (radj_row_l_low_level_spec)))) (PreH11 : (0 <= u_pre)) (PreH12 : (u_pre < n_pre)) (PreH13 : (n_pre <= INT_MAX)) (PreH14 : (0 <= timer_m)) (PreH15 : (timer_m < (count_nonzero (vis1_m)))) (PreH16 : (((count_nonzero (vis1_m)) - timer_m ) = (((count_nonzero (vis1_l_low_level_spec)) - timer_v_low_level_spec ) + 1 ))) ,
  (IntArray.full fin_pre n_pre (replace_Znth (u_pre) ((Znth 0 (cons (timer_m) ((@nil Z))) 0)) (fin_m)) )
  **  (IntArray.full timer_p_pre 1 (cons (timer_m) ((@nil Z))) )
  **  ((( &( "t0" ) )) # Int  |-> (Znth 0 (cons (timer_m) ((@nil Z))) 0))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "u" ) )) # Int  |-> u_pre)
  **  ((( &( "radj_col" ) )) # Ptr  |-> radj_col_pre)
  **  ((( &( "radj_row" ) )) # Ptr  |-> radj_row_pre)
  **  ((( &( "vis1" ) )) # Ptr  |-> vis1_pre)
  **  ((( &( "fin" ) )) # Ptr  |-> fin_pre)
  **  ((( &( "timer_p" ) )) # Ptr  |-> timer_p_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  (IntArray.full radj_col_pre (m_of (radj_row_l_low_level_spec)) radj_col_l_low_level_spec )
  **  (IntArray.full radj_row_pre (n_pre + 1 ) radj_row_l_low_level_spec )
  **  (IntArray.full vis1_pre n_pre vis1_m )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition dfs1_entail_wit_1 := 
(
forall (timer_p_pre: Z) (fin_pre: Z) (vis1_pre: Z) (radj_row_pre: Z) (radj_col_pre: Z) (n_pre: Z) (u_pre: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (timer_v_low_level_spec: Z) (fin_l_low_level_spec: (@list Z)) (vis1_l_low_level_spec: (@list Z)) (radj_row_l_low_level_spec: (@list Z)) (radj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (PreH1 : (csr_wf1 g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_l_low_level_spec fin_l_low_level_spec )) (PreH2 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH3 : (safeExec (pre_dfs1 (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (vis1_l_low_level_spec) (fin_l_low_level_spec) (timer_v_low_level_spec)) (dfs_finish (g_low_level_spec) (u_pre)) X_low_level_spec )) (PreH4 : (0 <= u_pre)) (PreH5 : (u_pre < n_pre)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : ((Znth (u_pre) (vis1_l_low_level_spec) (0)) = 0)) (PreH8 : (0 <= timer_v_low_level_spec)) (PreH9 : (timer_v_low_level_spec <= (count_nonzero (vis1_l_low_level_spec)))) ,
  (IntArray.full radj_row_pre (n_pre + 1 ) radj_row_l_low_level_spec )
  **  (IntArray.full vis1_pre n_pre (replace_Znth (u_pre) (1) (vis1_l_low_level_spec)) )
  **  (IntArray.full radj_col_pre (m_of (radj_row_l_low_level_spec)) radj_col_l_low_level_spec )
  **  (IntArray.full fin_pre n_pre fin_l_low_level_spec )
  **  (IntArray.full timer_p_pre 1 (cons (timer_v_low_level_spec) ((@nil Z))) )
|--
  EX (timer_m: Z)  (vis1_m: (@list Z))  (fin_m: (@list Z)) ,
  “ (csr_wf1 g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_m fin_m ) ” 
  &&  “ ((adj_verts (g_low_level_spec)) = n_pre) ” 
  &&  “ (safeExec (pre_dfs1 (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (vis1_m) (fin_m) (timer_m)) (dfs_finish_from (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (u_pre) ((Znth u_pre radj_row_l_low_level_spec 0))) X_low_level_spec ) ” 
  &&  “ ((Znth u_pre radj_row_l_low_level_spec 0) = (csr_lo (u_pre) (radj_row_l_low_level_spec))) ” 
  &&  “ ((Znth (u_pre + 1 ) radj_row_l_low_level_spec 0) = (csr_hi (u_pre) (radj_row_l_low_level_spec))) ” 
  &&  “ (0 <= (Znth u_pre radj_row_l_low_level_spec 0)) ” 
  &&  “ ((Znth u_pre radj_row_l_low_level_spec 0) <= (Znth u_pre radj_row_l_low_level_spec 0)) ” 
  &&  “ ((Znth u_pre radj_row_l_low_level_spec 0) <= (Znth (u_pre + 1 ) radj_row_l_low_level_spec 0)) ” 
  &&  “ ((Znth (u_pre + 1 ) radj_row_l_low_level_spec 0) <= (m_of (radj_row_l_low_level_spec))) ” 
  &&  “ (0 <= u_pre) ” 
  &&  “ (u_pre < n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (0 <= timer_m) ” 
  &&  “ (timer_m < (count_nonzero (vis1_m))) ” 
  &&  “ (((count_nonzero (vis1_m)) - timer_m ) = (((count_nonzero (vis1_l_low_level_spec)) - timer_v_low_level_spec ) + 1 )) ”
  &&  (IntArray.full radj_col_pre (m_of (radj_row_l_low_level_spec)) radj_col_l_low_level_spec )
  **  (IntArray.full radj_row_pre (n_pre + 1 ) radj_row_l_low_level_spec )
  **  (IntArray.full vis1_pre n_pre vis1_m )
  **  (IntArray.full fin_pre n_pre fin_m )
  **  (IntArray.full timer_p_pre 1 (cons (timer_m) ((@nil Z))) )
) \/
(
forall (n_pre: Z) (u_pre: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (timer_v_low_level_spec: Z) (fin_l_low_level_spec: (@list Z)) (vis1_l_low_level_spec: (@list Z)) (radj_row_l_low_level_spec: (@list Z)) (radj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (PreH1 : (csr_wf1 g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_l_low_level_spec fin_l_low_level_spec )) (PreH2 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH3 : (safeExec (pre_dfs1 (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (vis1_l_low_level_spec) (fin_l_low_level_spec) (timer_v_low_level_spec)) (dfs_finish (g_low_level_spec) (u_pre)) X_low_level_spec )) (PreH4 : (0 <= u_pre)) (PreH5 : (u_pre < n_pre)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : ((Znth (u_pre) (vis1_l_low_level_spec) (0)) = 0)) (PreH8 : (0 <= timer_v_low_level_spec)) (PreH9 : (timer_v_low_level_spec <= (count_nonzero (vis1_l_low_level_spec)))) ,
  TT && emp 
|--
  EX (timer_m: Z) ,
  “ ((cons (timer_v_low_level_spec) ((@nil Z))) = (cons (timer_m) ((@nil Z)))) ” 
  &&  “ (csr_wf1 g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec (replace_Znth (u_pre) (1) (vis1_l_low_level_spec)) fin_l_low_level_spec ) ” 
  &&  “ ((adj_verts (g_low_level_spec)) = n_pre) ” 
  &&  “ (safeExec (pre_dfs1 (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) ((replace_Znth (u_pre) (1) (vis1_l_low_level_spec))) (fin_l_low_level_spec) (timer_m)) (dfs_finish_from (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (u_pre) ((Znth u_pre radj_row_l_low_level_spec 0))) X_low_level_spec ) ” 
  &&  “ ((Znth u_pre radj_row_l_low_level_spec 0) = (csr_lo (u_pre) (radj_row_l_low_level_spec))) ” 
  &&  “ ((Znth (u_pre + 1 ) radj_row_l_low_level_spec 0) = (csr_hi (u_pre) (radj_row_l_low_level_spec))) ” 
  &&  “ (0 <= (Znth u_pre radj_row_l_low_level_spec 0)) ” 
  &&  “ ((Znth u_pre radj_row_l_low_level_spec 0) <= (Znth u_pre radj_row_l_low_level_spec 0)) ” 
  &&  “ ((Znth u_pre radj_row_l_low_level_spec 0) <= (Znth (u_pre + 1 ) radj_row_l_low_level_spec 0)) ” 
  &&  “ ((Znth (u_pre + 1 ) radj_row_l_low_level_spec 0) <= (m_of (radj_row_l_low_level_spec))) ” 
  &&  “ (0 <= u_pre) ” 
  &&  “ (u_pre < n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (0 <= timer_m) ” 
  &&  “ (timer_m < (count_nonzero ((replace_Znth (u_pre) (1) (vis1_l_low_level_spec))))) ” 
  &&  “ (((count_nonzero ((replace_Znth (u_pre) (1) (vis1_l_low_level_spec)))) - timer_m ) = (((count_nonzero (vis1_l_low_level_spec)) - timer_v_low_level_spec ) + 1 )) ”
  &&  emp
).

Definition dfs1_entail_wit_2 := 
(
forall (timer_p_pre: Z) (fin_pre: Z) (vis1_pre: Z) (radj_row_pre: Z) (radj_col_pre: Z) (n_pre: Z) (u_pre: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (timer_v_low_level_spec: Z) (vis1_l_low_level_spec: (@list Z)) (radj_row_l_low_level_spec: (@list Z)) (radj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (hi: Z) (lo: Z) (i: Z) (vis1_m: (@list Z)) (fin_m: (@list Z)) (timer_m: Z) (PreH1 : (i < hi)) (PreH2 : (csr_wf1 g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_m fin_m )) (PreH3 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH4 : (safeExec (pre_dfs1 (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (vis1_m) (fin_m) (timer_m)) (dfs_finish_from (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (u_pre) (i)) X_low_level_spec )) (PreH5 : (lo = (csr_lo (u_pre) (radj_row_l_low_level_spec)))) (PreH6 : (hi = (csr_hi (u_pre) (radj_row_l_low_level_spec)))) (PreH7 : (0 <= lo)) (PreH8 : (lo <= i)) (PreH9 : (i <= hi)) (PreH10 : (hi <= (m_of (radj_row_l_low_level_spec)))) (PreH11 : (0 <= u_pre)) (PreH12 : (u_pre < n_pre)) (PreH13 : (n_pre <= INT_MAX)) (PreH14 : (0 <= timer_m)) (PreH15 : (timer_m < (count_nonzero (vis1_m)))) (PreH16 : (((count_nonzero (vis1_m)) - timer_m ) = (((count_nonzero (vis1_l_low_level_spec)) - timer_v_low_level_spec ) + 1 ))) ,
  (IntArray.full radj_col_pre (m_of (radj_row_l_low_level_spec)) radj_col_l_low_level_spec )
  **  (IntArray.full radj_row_pre (n_pre + 1 ) radj_row_l_low_level_spec )
  **  (IntArray.full vis1_pre n_pre vis1_m )
  **  (IntArray.full fin_pre n_pre fin_m )
  **  (IntArray.full timer_p_pre 1 (cons (timer_m) ((@nil Z))) )
|--
  “ (csr_wf1 g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_m fin_m ) ” 
  &&  “ ((adj_verts (g_low_level_spec)) = n_pre) ” 
  &&  “ (safeExec (pre_dfs1 (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (vis1_m) (fin_m) (timer_m)) (dfs_finish_from (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (u_pre) (i)) X_low_level_spec ) ” 
  &&  “ (lo = (csr_lo (u_pre) (radj_row_l_low_level_spec))) ” 
  &&  “ (hi = (csr_hi (u_pre) (radj_row_l_low_level_spec))) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= i) ” 
  &&  “ (i < hi) ” 
  &&  “ (hi <= (m_of (radj_row_l_low_level_spec))) ” 
  &&  “ (0 <= u_pre) ” 
  &&  “ (u_pre < n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (0 <= timer_m) ” 
  &&  “ (timer_m < (count_nonzero (vis1_m))) ” 
  &&  “ (((count_nonzero (vis1_m)) - timer_m ) = (((count_nonzero (vis1_l_low_level_spec)) - timer_v_low_level_spec ) + 1 )) ” 
  &&  “ (0 <= (Znth i radj_col_l_low_level_spec 0)) ” 
  &&  “ ((Znth i radj_col_l_low_level_spec 0) < n_pre) ” 
  &&  “ ((Znth i radj_col_l_low_level_spec 0) = (Znth (i) (radj_col_l_low_level_spec) (0))) ”
  &&  (IntArray.full radj_col_pre (m_of (radj_row_l_low_level_spec)) radj_col_l_low_level_spec )
  **  (IntArray.full radj_row_pre (n_pre + 1 ) radj_row_l_low_level_spec )
  **  (IntArray.full vis1_pre n_pre vis1_m )
  **  (IntArray.full fin_pre n_pre fin_m )
  **  (IntArray.full timer_p_pre 1 (cons (timer_m) ((@nil Z))) )
) \/
(
forall (n_pre: Z) (u_pre: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (timer_v_low_level_spec: Z) (vis1_l_low_level_spec: (@list Z)) (radj_row_l_low_level_spec: (@list Z)) (radj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (hi: Z) (lo: Z) (i: Z) (vis1_m: (@list Z)) (fin_m: (@list Z)) (timer_m: Z) (PreH1 : (i < hi)) (PreH2 : (csr_wf1 g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_m fin_m )) (PreH3 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH4 : (safeExec (pre_dfs1 (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (vis1_m) (fin_m) (timer_m)) (dfs_finish_from (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (u_pre) (i)) X_low_level_spec )) (PreH5 : (lo = (csr_lo (u_pre) (radj_row_l_low_level_spec)))) (PreH6 : (hi = (csr_hi (u_pre) (radj_row_l_low_level_spec)))) (PreH7 : (0 <= lo)) (PreH8 : (lo <= i)) (PreH9 : (i <= hi)) (PreH10 : (hi <= (m_of (radj_row_l_low_level_spec)))) (PreH11 : (0 <= u_pre)) (PreH12 : (u_pre < n_pre)) (PreH13 : (n_pre <= INT_MAX)) (PreH14 : (0 <= timer_m)) (PreH15 : (timer_m < (count_nonzero (vis1_m)))) (PreH16 : (((count_nonzero (vis1_m)) - timer_m ) = (((count_nonzero (vis1_l_low_level_spec)) - timer_v_low_level_spec ) + 1 ))) ,
  TT && emp 
|--
  “ ((Znth i radj_col_l_low_level_spec 0) = (Znth (i) (radj_col_l_low_level_spec) (0))) ” 
  &&  “ ((Znth i radj_col_l_low_level_spec 0) < n_pre) ” 
  &&  “ (0 <= (Znth i radj_col_l_low_level_spec 0)) ”
  &&  emp
).

Definition dfs1_entail_wit_2_split_goal_1 := 
forall (n_pre: Z) (u_pre: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (timer_v_low_level_spec: Z) (vis1_l_low_level_spec: (@list Z)) (radj_row_l_low_level_spec: (@list Z)) (radj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (hi: Z) (lo: Z) (i: Z) (vis1_m: (@list Z)) (fin_m: (@list Z)) (timer_m: Z) (PreH1 : (i < hi)) (PreH2 : (csr_wf1 g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_m fin_m )) (PreH3 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH4 : (safeExec (pre_dfs1 (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (vis1_m) (fin_m) (timer_m)) (dfs_finish_from (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (u_pre) (i)) X_low_level_spec )) (PreH5 : (lo = (csr_lo (u_pre) (radj_row_l_low_level_spec)))) (PreH6 : (hi = (csr_hi (u_pre) (radj_row_l_low_level_spec)))) (PreH7 : (0 <= lo)) (PreH8 : (lo <= i)) (PreH9 : (i <= hi)) (PreH10 : (hi <= (m_of (radj_row_l_low_level_spec)))) (PreH11 : (0 <= u_pre)) (PreH12 : (u_pre < n_pre)) (PreH13 : (n_pre <= INT_MAX)) (PreH14 : (0 <= timer_m)) (PreH15 : (timer_m < (count_nonzero (vis1_m)))) (PreH16 : (((count_nonzero (vis1_m)) - timer_m ) = (((count_nonzero (vis1_l_low_level_spec)) - timer_v_low_level_spec ) + 1 ))) ,
  TT && emp 
|--
  “ ((Znth i radj_col_l_low_level_spec 0) = (Znth (i) (radj_col_l_low_level_spec) (0))) ”
.

Definition dfs1_entail_wit_2_split_goal_2 := 
forall (n_pre: Z) (u_pre: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (timer_v_low_level_spec: Z) (vis1_l_low_level_spec: (@list Z)) (radj_row_l_low_level_spec: (@list Z)) (radj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (hi: Z) (lo: Z) (i: Z) (vis1_m: (@list Z)) (fin_m: (@list Z)) (timer_m: Z) (PreH1 : (i < hi)) (PreH2 : (csr_wf1 g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_m fin_m )) (PreH3 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH4 : (safeExec (pre_dfs1 (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (vis1_m) (fin_m) (timer_m)) (dfs_finish_from (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (u_pre) (i)) X_low_level_spec )) (PreH5 : (lo = (csr_lo (u_pre) (radj_row_l_low_level_spec)))) (PreH6 : (hi = (csr_hi (u_pre) (radj_row_l_low_level_spec)))) (PreH7 : (0 <= lo)) (PreH8 : (lo <= i)) (PreH9 : (i <= hi)) (PreH10 : (hi <= (m_of (radj_row_l_low_level_spec)))) (PreH11 : (0 <= u_pre)) (PreH12 : (u_pre < n_pre)) (PreH13 : (n_pre <= INT_MAX)) (PreH14 : (0 <= timer_m)) (PreH15 : (timer_m < (count_nonzero (vis1_m)))) (PreH16 : (((count_nonzero (vis1_m)) - timer_m ) = (((count_nonzero (vis1_l_low_level_spec)) - timer_v_low_level_spec ) + 1 ))) ,
  TT && emp 
|--
  “ ((Znth i radj_col_l_low_level_spec 0) < n_pre) ”
.

Definition dfs1_entail_wit_2_split_goal_3 := 
forall (n_pre: Z) (u_pre: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (timer_v_low_level_spec: Z) (vis1_l_low_level_spec: (@list Z)) (radj_row_l_low_level_spec: (@list Z)) (radj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (hi: Z) (lo: Z) (i: Z) (vis1_m: (@list Z)) (fin_m: (@list Z)) (timer_m: Z) (PreH1 : (i < hi)) (PreH2 : (csr_wf1 g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_m fin_m )) (PreH3 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH4 : (safeExec (pre_dfs1 (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (vis1_m) (fin_m) (timer_m)) (dfs_finish_from (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (u_pre) (i)) X_low_level_spec )) (PreH5 : (lo = (csr_lo (u_pre) (radj_row_l_low_level_spec)))) (PreH6 : (hi = (csr_hi (u_pre) (radj_row_l_low_level_spec)))) (PreH7 : (0 <= lo)) (PreH8 : (lo <= i)) (PreH9 : (i <= hi)) (PreH10 : (hi <= (m_of (radj_row_l_low_level_spec)))) (PreH11 : (0 <= u_pre)) (PreH12 : (u_pre < n_pre)) (PreH13 : (n_pre <= INT_MAX)) (PreH14 : (0 <= timer_m)) (PreH15 : (timer_m < (count_nonzero (vis1_m)))) (PreH16 : (((count_nonzero (vis1_m)) - timer_m ) = (((count_nonzero (vis1_l_low_level_spec)) - timer_v_low_level_spec ) + 1 ))) ,
  TT && emp 
|--
  “ (0 <= (Znth i radj_col_l_low_level_spec 0)) ”
.

Definition dfs1_entail_wit_3_1 := 
(
forall (timer_p_pre: Z) (fin_pre: Z) (vis1_pre: Z) (radj_row_pre: Z) (radj_col_pre: Z) (n_pre: Z) (u_pre: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (timer_v_low_level_spec: Z) (vis1_l_low_level_spec: (@list Z)) (radj_row_l_low_level_spec: (@list Z)) (radj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (vis1_m_2: (@list Z)) (fin_m_2: (@list Z)) (timer_m_2: Z) (i: Z) (lo: Z) (hi: Z) (v: Z) (timer_v_: Z) (vis1_l_: (@list Z)) (fin_l_: (@list Z)) (PreH1 : (csr_wf1 g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_l_ fin_l_ )) (PreH2 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH3 : (safeExec (pre_dfs1 (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (vis1_l_) (fin_l_) (timer_v_)) (applyf ((dfs_finish_fromK (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (u_pre) ((i + 1 )))) (tt)) X_low_level_spec )) (PreH4 : (0 <= timer_v_)) (PreH5 : (((count_nonzero (vis1_l_)) - timer_v_ ) = ((count_nonzero (vis1_m_2)) - timer_m_2 ))) (PreH6 : ((Znth v vis1_m_2 0) = 0)) (PreH7 : (csr_wf1 g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_m_2 fin_m_2 )) (PreH8 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH9 : (lo = (csr_lo (u_pre) (radj_row_l_low_level_spec)))) (PreH10 : (hi = (csr_hi (u_pre) (radj_row_l_low_level_spec)))) (PreH11 : (0 <= lo)) (PreH12 : (lo <= i)) (PreH13 : (i < hi)) (PreH14 : (hi <= (m_of (radj_row_l_low_level_spec)))) (PreH15 : (0 <= u_pre)) (PreH16 : (u_pre < n_pre)) (PreH17 : (n_pre <= INT_MAX)) (PreH18 : (0 <= timer_m_2)) (PreH19 : (timer_m_2 < (count_nonzero (vis1_m_2)))) (PreH20 : (((count_nonzero (vis1_m_2)) - timer_m_2 ) = (((count_nonzero (vis1_l_low_level_spec)) - timer_v_low_level_spec ) + 1 ))) (PreH21 : (0 <= v)) (PreH22 : (v < n_pre)) (PreH23 : (v = (Znth (i) (radj_col_l_low_level_spec) (0)))) ,
  (IntArray.full radj_col_pre (m_of (radj_row_l_low_level_spec)) radj_col_l_low_level_spec )
  **  (IntArray.full radj_row_pre (n_pre + 1 ) radj_row_l_low_level_spec )
  **  (IntArray.full vis1_pre n_pre vis1_l_ )
  **  (IntArray.full fin_pre n_pre fin_l_ )
  **  (IntArray.full timer_p_pre 1 (cons (timer_v_) ((@nil Z))) )
|--
  EX (timer_m: Z)  (vis1_m: (@list Z))  (fin_m: (@list Z)) ,
  “ (csr_wf1 g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_m fin_m ) ” 
  &&  “ ((adj_verts (g_low_level_spec)) = n_pre) ” 
  &&  “ (safeExec (pre_dfs1 (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (vis1_m) (fin_m) (timer_m)) (dfs_finish_from (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (u_pre) ((i + 1 ))) X_low_level_spec ) ” 
  &&  “ (lo = (csr_lo (u_pre) (radj_row_l_low_level_spec))) ” 
  &&  “ (hi = (csr_hi (u_pre) (radj_row_l_low_level_spec))) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= hi) ” 
  &&  “ (hi <= (m_of (radj_row_l_low_level_spec))) ” 
  &&  “ (0 <= u_pre) ” 
  &&  “ (u_pre < n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (0 <= timer_m) ” 
  &&  “ (timer_m < (count_nonzero (vis1_m))) ” 
  &&  “ (((count_nonzero (vis1_m)) - timer_m ) = (((count_nonzero (vis1_l_low_level_spec)) - timer_v_low_level_spec ) + 1 )) ”
  &&  (IntArray.full radj_col_pre (m_of (radj_row_l_low_level_spec)) radj_col_l_low_level_spec )
  **  (IntArray.full radj_row_pre (n_pre + 1 ) radj_row_l_low_level_spec )
  **  (IntArray.full vis1_pre n_pre vis1_m )
  **  (IntArray.full fin_pre n_pre fin_m )
  **  (IntArray.full timer_p_pre 1 (cons (timer_m) ((@nil Z))) )
) \/
(
forall (n_pre: Z) (u_pre: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (timer_v_low_level_spec: Z) (vis1_l_low_level_spec: (@list Z)) (radj_row_l_low_level_spec: (@list Z)) (radj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (vis1_m_2: (@list Z)) (fin_m_2: (@list Z)) (timer_m_2: Z) (i: Z) (lo: Z) (hi: Z) (v: Z) (timer_v_: Z) (vis1_l_: (@list Z)) (fin_l_: (@list Z)) (PreH1 : (csr_wf1 g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_l_ fin_l_ )) (PreH2 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH3 : (safeExec (pre_dfs1 (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (vis1_l_) (fin_l_) (timer_v_)) (applyf ((dfs_finish_fromK (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (u_pre) ((i + 1 )))) (tt)) X_low_level_spec )) (PreH4 : (0 <= timer_v_)) (PreH5 : (((count_nonzero (vis1_l_)) - timer_v_ ) = ((count_nonzero (vis1_m_2)) - timer_m_2 ))) (PreH6 : ((Znth v vis1_m_2 0) = 0)) (PreH7 : (csr_wf1 g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_m_2 fin_m_2 )) (PreH8 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH9 : (lo = (csr_lo (u_pre) (radj_row_l_low_level_spec)))) (PreH10 : (hi = (csr_hi (u_pre) (radj_row_l_low_level_spec)))) (PreH11 : (0 <= lo)) (PreH12 : (lo <= i)) (PreH13 : (i < hi)) (PreH14 : (hi <= (m_of (radj_row_l_low_level_spec)))) (PreH15 : (0 <= u_pre)) (PreH16 : (u_pre < n_pre)) (PreH17 : (n_pre <= INT_MAX)) (PreH18 : (0 <= timer_m_2)) (PreH19 : (timer_m_2 < (count_nonzero (vis1_m_2)))) (PreH20 : (((count_nonzero (vis1_m_2)) - timer_m_2 ) = (((count_nonzero (vis1_l_low_level_spec)) - timer_v_low_level_spec ) + 1 ))) (PreH21 : (0 <= v)) (PreH22 : (v < n_pre)) (PreH23 : (v = (Znth (i) (radj_col_l_low_level_spec) (0)))) ,
  TT && emp 
|--
  EX (timer_m: Z) ,
  “ ((cons (timer_v_) ((@nil Z))) = (cons (timer_m) ((@nil Z)))) ” 
  &&  “ (csr_wf1 g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_l_ fin_l_ ) ” 
  &&  “ ((adj_verts (g_low_level_spec)) = n_pre) ” 
  &&  “ (safeExec (pre_dfs1 (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (vis1_l_) (fin_l_) (timer_m)) (dfs_finish_from (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (u_pre) ((i + 1 ))) X_low_level_spec ) ” 
  &&  “ (lo = (csr_lo (u_pre) (radj_row_l_low_level_spec))) ” 
  &&  “ (hi = (csr_hi (u_pre) (radj_row_l_low_level_spec))) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= hi) ” 
  &&  “ (hi <= (m_of (radj_row_l_low_level_spec))) ” 
  &&  “ (0 <= u_pre) ” 
  &&  “ (u_pre < n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (0 <= timer_m) ” 
  &&  “ (timer_m < (count_nonzero (vis1_l_))) ” 
  &&  “ (((count_nonzero (vis1_l_)) - timer_m ) = (((count_nonzero (vis1_l_low_level_spec)) - timer_v_low_level_spec ) + 1 )) ”
  &&  emp
).

Definition dfs1_entail_wit_3_2 := 
(
forall (timer_p_pre: Z) (fin_pre: Z) (vis1_pre: Z) (radj_row_pre: Z) (radj_col_pre: Z) (n_pre: Z) (u_pre: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (timer_v_low_level_spec: Z) (vis1_l_low_level_spec: (@list Z)) (radj_row_l_low_level_spec: (@list Z)) (radj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (vis1_m_2: (@list Z)) (fin_m_2: (@list Z)) (timer_m_2: Z) (i: Z) (lo: Z) (hi: Z) (v: Z) (PreH1 : ((Znth v vis1_m_2 0) <> 0)) (PreH2 : (csr_wf1 g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_m_2 fin_m_2 )) (PreH3 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH4 : (safeExec (pre_dfs1 (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (vis1_m_2) (fin_m_2) (timer_m_2)) (dfs_finish_from (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (u_pre) (i)) X_low_level_spec )) (PreH5 : (lo = (csr_lo (u_pre) (radj_row_l_low_level_spec)))) (PreH6 : (hi = (csr_hi (u_pre) (radj_row_l_low_level_spec)))) (PreH7 : (0 <= lo)) (PreH8 : (lo <= i)) (PreH9 : (i < hi)) (PreH10 : (hi <= (m_of (radj_row_l_low_level_spec)))) (PreH11 : (0 <= u_pre)) (PreH12 : (u_pre < n_pre)) (PreH13 : (n_pre <= INT_MAX)) (PreH14 : (0 <= timer_m_2)) (PreH15 : (timer_m_2 < (count_nonzero (vis1_m_2)))) (PreH16 : (((count_nonzero (vis1_m_2)) - timer_m_2 ) = (((count_nonzero (vis1_l_low_level_spec)) - timer_v_low_level_spec ) + 1 ))) (PreH17 : (0 <= v)) (PreH18 : (v < n_pre)) (PreH19 : (v = (Znth (i) (radj_col_l_low_level_spec) (0)))) ,
  (IntArray.full vis1_pre n_pre vis1_m_2 )
  **  (IntArray.full radj_col_pre (m_of (radj_row_l_low_level_spec)) radj_col_l_low_level_spec )
  **  (IntArray.full radj_row_pre (n_pre + 1 ) radj_row_l_low_level_spec )
  **  (IntArray.full fin_pre n_pre fin_m_2 )
  **  (IntArray.full timer_p_pre 1 (cons (timer_m_2) ((@nil Z))) )
|--
  EX (timer_m: Z)  (vis1_m: (@list Z))  (fin_m: (@list Z)) ,
  “ (csr_wf1 g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_m fin_m ) ” 
  &&  “ ((adj_verts (g_low_level_spec)) = n_pre) ” 
  &&  “ (safeExec (pre_dfs1 (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (vis1_m) (fin_m) (timer_m)) (dfs_finish_from (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (u_pre) ((i + 1 ))) X_low_level_spec ) ” 
  &&  “ (lo = (csr_lo (u_pre) (radj_row_l_low_level_spec))) ” 
  &&  “ (hi = (csr_hi (u_pre) (radj_row_l_low_level_spec))) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= hi) ” 
  &&  “ (hi <= (m_of (radj_row_l_low_level_spec))) ” 
  &&  “ (0 <= u_pre) ” 
  &&  “ (u_pre < n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (0 <= timer_m) ” 
  &&  “ (timer_m < (count_nonzero (vis1_m))) ” 
  &&  “ (((count_nonzero (vis1_m)) - timer_m ) = (((count_nonzero (vis1_l_low_level_spec)) - timer_v_low_level_spec ) + 1 )) ”
  &&  (IntArray.full radj_col_pre (m_of (radj_row_l_low_level_spec)) radj_col_l_low_level_spec )
  **  (IntArray.full radj_row_pre (n_pre + 1 ) radj_row_l_low_level_spec )
  **  (IntArray.full vis1_pre n_pre vis1_m )
  **  (IntArray.full fin_pre n_pre fin_m )
  **  (IntArray.full timer_p_pre 1 (cons (timer_m) ((@nil Z))) )
) \/
(
forall (n_pre: Z) (u_pre: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (timer_v_low_level_spec: Z) (vis1_l_low_level_spec: (@list Z)) (radj_row_l_low_level_spec: (@list Z)) (radj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (vis1_m_2: (@list Z)) (fin_m_2: (@list Z)) (timer_m_2: Z) (i: Z) (lo: Z) (hi: Z) (v: Z) (PreH1 : ((Znth v vis1_m_2 0) <> 0)) (PreH2 : (csr_wf1 g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_m_2 fin_m_2 )) (PreH3 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH4 : (safeExec (pre_dfs1 (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (vis1_m_2) (fin_m_2) (timer_m_2)) (dfs_finish_from (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (u_pre) (i)) X_low_level_spec )) (PreH5 : (lo = (csr_lo (u_pre) (radj_row_l_low_level_spec)))) (PreH6 : (hi = (csr_hi (u_pre) (radj_row_l_low_level_spec)))) (PreH7 : (0 <= lo)) (PreH8 : (lo <= i)) (PreH9 : (i < hi)) (PreH10 : (hi <= (m_of (radj_row_l_low_level_spec)))) (PreH11 : (0 <= u_pre)) (PreH12 : (u_pre < n_pre)) (PreH13 : (n_pre <= INT_MAX)) (PreH14 : (0 <= timer_m_2)) (PreH15 : (timer_m_2 < (count_nonzero (vis1_m_2)))) (PreH16 : (((count_nonzero (vis1_m_2)) - timer_m_2 ) = (((count_nonzero (vis1_l_low_level_spec)) - timer_v_low_level_spec ) + 1 ))) (PreH17 : (0 <= v)) (PreH18 : (v < n_pre)) (PreH19 : (v = (Znth (i) (radj_col_l_low_level_spec) (0)))) ,
  TT && emp 
|--
  EX (timer_m: Z) ,
  “ ((cons (timer_m_2) ((@nil Z))) = (cons (timer_m) ((@nil Z)))) ” 
  &&  “ (csr_wf1 g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_m_2 fin_m_2 ) ” 
  &&  “ ((adj_verts (g_low_level_spec)) = n_pre) ” 
  &&  “ (safeExec (pre_dfs1 (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (vis1_m_2) (fin_m_2) (timer_m)) (dfs_finish_from (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (u_pre) ((i + 1 ))) X_low_level_spec ) ” 
  &&  “ (lo = (csr_lo (u_pre) (radj_row_l_low_level_spec))) ” 
  &&  “ (hi = (csr_hi (u_pre) (radj_row_l_low_level_spec))) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= hi) ” 
  &&  “ (hi <= (m_of (radj_row_l_low_level_spec))) ” 
  &&  “ (0 <= u_pre) ” 
  &&  “ (u_pre < n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (0 <= timer_m) ” 
  &&  “ (timer_m < (count_nonzero (vis1_m_2))) ” 
  &&  “ (((count_nonzero (vis1_m_2)) - timer_m ) = (((count_nonzero (vis1_l_low_level_spec)) - timer_v_low_level_spec ) + 1 )) ”
  &&  emp
).

Definition dfs1_return_wit_1 := 
(
forall (timer_p_pre: Z) (fin_pre: Z) (vis1_pre: Z) (radj_row_pre: Z) (radj_col_pre: Z) (n_pre: Z) (u_pre: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (timer_v_low_level_spec: Z) (vis1_l_low_level_spec: (@list Z)) (radj_row_l_low_level_spec: (@list Z)) (radj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (hi: Z) (lo: Z) (timer_m: Z) (i: Z) (vis1_m: (@list Z)) (fin_m: (@list Z)) (PreH1 : (i >= hi)) (PreH2 : (csr_wf1 g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_m fin_m )) (PreH3 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH4 : (safeExec (pre_dfs1 (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (vis1_m) (fin_m) (timer_m)) (dfs_finish_from (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (u_pre) (i)) X_low_level_spec )) (PreH5 : (lo = (csr_lo (u_pre) (radj_row_l_low_level_spec)))) (PreH6 : (hi = (csr_hi (u_pre) (radj_row_l_low_level_spec)))) (PreH7 : (0 <= lo)) (PreH8 : (lo <= i)) (PreH9 : (i <= hi)) (PreH10 : (hi <= (m_of (radj_row_l_low_level_spec)))) (PreH11 : (0 <= u_pre)) (PreH12 : (u_pre < n_pre)) (PreH13 : (n_pre <= INT_MAX)) (PreH14 : (0 <= timer_m)) (PreH15 : (timer_m < (count_nonzero (vis1_m)))) (PreH16 : (((count_nonzero (vis1_m)) - timer_m ) = (((count_nonzero (vis1_l_low_level_spec)) - timer_v_low_level_spec ) + 1 ))) ,
  (IntArray.full timer_p_pre 1 (replace_Znth (0) (((Znth 0 (cons (timer_m) ((@nil Z))) 0) + 1 )) ((cons (timer_m) ((@nil Z))))) )
  **  (IntArray.full fin_pre n_pre (replace_Znth (u_pre) ((Znth 0 (cons (timer_m) ((@nil Z))) 0)) (fin_m)) )
  **  (IntArray.full radj_col_pre (m_of (radj_row_l_low_level_spec)) radj_col_l_low_level_spec )
  **  (IntArray.full radj_row_pre (n_pre + 1 ) radj_row_l_low_level_spec )
  **  (IntArray.full vis1_pre n_pre vis1_m )
|--
  EX (timer_v_: Z)  (vis1_l_: (@list Z))  (fin_l_: (@list Z)) ,
  “ (csr_wf1 g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_l_ fin_l_ ) ” 
  &&  “ ((adj_verts (g_low_level_spec)) = n_pre) ” 
  &&  “ (safeExec (pre_dfs1 (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (vis1_l_) (fin_l_) (timer_v_)) (return (tt)) X_low_level_spec ) ” 
  &&  “ (0 <= timer_v_) ” 
  &&  “ (((count_nonzero (vis1_l_)) - timer_v_ ) = ((count_nonzero (vis1_l_low_level_spec)) - timer_v_low_level_spec )) ”
  &&  (IntArray.full radj_col_pre (m_of (radj_row_l_low_level_spec)) radj_col_l_low_level_spec )
  **  (IntArray.full radj_row_pre (n_pre + 1 ) radj_row_l_low_level_spec )
  **  (IntArray.full vis1_pre n_pre vis1_l_ )
  **  (IntArray.full fin_pre n_pre fin_l_ )
  **  (IntArray.full timer_p_pre 1 (cons (timer_v_) ((@nil Z))) )
) \/
(
forall (n_pre: Z) (u_pre: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (timer_v_low_level_spec: Z) (vis1_l_low_level_spec: (@list Z)) (radj_row_l_low_level_spec: (@list Z)) (radj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (hi: Z) (lo: Z) (timer_m: Z) (i: Z) (vis1_m: (@list Z)) (fin_m: (@list Z)) (PreH1 : (i >= hi)) (PreH2 : (csr_wf1 g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_m fin_m )) (PreH3 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH4 : (safeExec (pre_dfs1 (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (vis1_m) (fin_m) (timer_m)) (dfs_finish_from (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (u_pre) (i)) X_low_level_spec )) (PreH5 : (lo = (csr_lo (u_pre) (radj_row_l_low_level_spec)))) (PreH6 : (hi = (csr_hi (u_pre) (radj_row_l_low_level_spec)))) (PreH7 : (0 <= lo)) (PreH8 : (lo <= i)) (PreH9 : (i <= hi)) (PreH10 : (hi <= (m_of (radj_row_l_low_level_spec)))) (PreH11 : (0 <= u_pre)) (PreH12 : (u_pre < n_pre)) (PreH13 : (n_pre <= INT_MAX)) (PreH14 : (0 <= timer_m)) (PreH15 : (timer_m < (count_nonzero (vis1_m)))) (PreH16 : (((count_nonzero (vis1_m)) - timer_m ) = (((count_nonzero (vis1_l_low_level_spec)) - timer_v_low_level_spec ) + 1 ))) ,
  TT && emp 
|--
  EX (timer_v_: Z) ,
  “ ((replace_Znth (0) (((Znth 0 (cons (timer_m) ((@nil Z))) 0) + 1 )) ((cons (timer_m) ((@nil Z))))) = (cons (timer_v_) ((@nil Z)))) ” 
  &&  “ (csr_wf1 g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_m (replace_Znth (u_pre) ((Znth 0 (cons (timer_m) ((@nil Z))) 0)) (fin_m)) ) ” 
  &&  “ ((adj_verts (g_low_level_spec)) = n_pre) ” 
  &&  “ (safeExec (pre_dfs1 (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (vis1_m) ((replace_Znth (u_pre) ((Znth 0 (cons (timer_m) ((@nil Z))) 0)) (fin_m))) (timer_v_)) (return (tt)) X_low_level_spec ) ” 
  &&  “ (0 <= timer_v_) ” 
  &&  “ (((count_nonzero (vis1_m)) - timer_v_ ) = ((count_nonzero (vis1_l_low_level_spec)) - timer_v_low_level_spec )) ”
  &&  emp
).

Definition dfs1_partial_solve_wit_1 := 
forall (timer_p_pre: Z) (fin_pre: Z) (vis1_pre: Z) (radj_row_pre: Z) (radj_col_pre: Z) (n_pre: Z) (u_pre: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (timer_v_low_level_spec: Z) (fin_l_low_level_spec: (@list Z)) (vis1_l_low_level_spec: (@list Z)) (radj_row_l_low_level_spec: (@list Z)) (radj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (PreH1 : (csr_wf1 g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_l_low_level_spec fin_l_low_level_spec )) (PreH2 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH3 : (safeExec (pre_dfs1 (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (vis1_l_low_level_spec) (fin_l_low_level_spec) (timer_v_low_level_spec)) (dfs_finish (g_low_level_spec) (u_pre)) X_low_level_spec )) (PreH4 : (0 <= u_pre)) (PreH5 : (u_pre < n_pre)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : ((Znth (u_pre) (vis1_l_low_level_spec) (0)) = 0)) (PreH8 : (0 <= timer_v_low_level_spec)) (PreH9 : (timer_v_low_level_spec <= (count_nonzero (vis1_l_low_level_spec)))) ,
  (IntArray.full radj_col_pre (m_of (radj_row_l_low_level_spec)) radj_col_l_low_level_spec )
  **  (IntArray.full radj_row_pre (n_pre + 1 ) radj_row_l_low_level_spec )
  **  (IntArray.full vis1_pre n_pre vis1_l_low_level_spec )
  **  (IntArray.full fin_pre n_pre fin_l_low_level_spec )
  **  (IntArray.full timer_p_pre 1 (cons (timer_v_low_level_spec) ((@nil Z))) )
|--
  “ (csr_wf1 g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_l_low_level_spec fin_l_low_level_spec ) ” 
  &&  “ ((adj_verts (g_low_level_spec)) = n_pre) ” 
  &&  “ (safeExec (pre_dfs1 (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (vis1_l_low_level_spec) (fin_l_low_level_spec) (timer_v_low_level_spec)) (dfs_finish (g_low_level_spec) (u_pre)) X_low_level_spec ) ” 
  &&  “ (0 <= u_pre) ” 
  &&  “ (u_pre < n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ ((Znth (u_pre) (vis1_l_low_level_spec) (0)) = 0) ” 
  &&  “ (0 <= timer_v_low_level_spec) ” 
  &&  “ (timer_v_low_level_spec <= (count_nonzero (vis1_l_low_level_spec))) ”
  &&  (((vis1_pre + (u_pre * sizeof(INT) ) )) # Int  |->_)
  **  (IntArray.missing_i vis1_pre u_pre 0 n_pre vis1_l_low_level_spec )
  **  (IntArray.full radj_col_pre (m_of (radj_row_l_low_level_spec)) radj_col_l_low_level_spec )
  **  (IntArray.full radj_row_pre (n_pre + 1 ) radj_row_l_low_level_spec )
  **  (IntArray.full fin_pre n_pre fin_l_low_level_spec )
  **  (IntArray.full timer_p_pre 1 (cons (timer_v_low_level_spec) ((@nil Z))) )
.

Definition dfs1_partial_solve_wit_2 := 
forall (timer_p_pre: Z) (fin_pre: Z) (vis1_pre: Z) (radj_row_pre: Z) (radj_col_pre: Z) (n_pre: Z) (u_pre: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (timer_v_low_level_spec: Z) (fin_l_low_level_spec: (@list Z)) (vis1_l_low_level_spec: (@list Z)) (radj_row_l_low_level_spec: (@list Z)) (radj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (PreH1 : (csr_wf1 g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_l_low_level_spec fin_l_low_level_spec )) (PreH2 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH3 : (safeExec (pre_dfs1 (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (vis1_l_low_level_spec) (fin_l_low_level_spec) (timer_v_low_level_spec)) (dfs_finish (g_low_level_spec) (u_pre)) X_low_level_spec )) (PreH4 : (0 <= u_pre)) (PreH5 : (u_pre < n_pre)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : ((Znth (u_pre) (vis1_l_low_level_spec) (0)) = 0)) (PreH8 : (0 <= timer_v_low_level_spec)) (PreH9 : (timer_v_low_level_spec <= (count_nonzero (vis1_l_low_level_spec)))) ,
  (IntArray.full vis1_pre n_pre (replace_Znth (u_pre) (1) (vis1_l_low_level_spec)) )
  **  (IntArray.full radj_col_pre (m_of (radj_row_l_low_level_spec)) radj_col_l_low_level_spec )
  **  (IntArray.full radj_row_pre (n_pre + 1 ) radj_row_l_low_level_spec )
  **  (IntArray.full fin_pre n_pre fin_l_low_level_spec )
  **  (IntArray.full timer_p_pre 1 (cons (timer_v_low_level_spec) ((@nil Z))) )
|--
  “ (csr_wf1 g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_l_low_level_spec fin_l_low_level_spec ) ” 
  &&  “ ((adj_verts (g_low_level_spec)) = n_pre) ” 
  &&  “ (safeExec (pre_dfs1 (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (vis1_l_low_level_spec) (fin_l_low_level_spec) (timer_v_low_level_spec)) (dfs_finish (g_low_level_spec) (u_pre)) X_low_level_spec ) ” 
  &&  “ (0 <= u_pre) ” 
  &&  “ (u_pre < n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ ((Znth (u_pre) (vis1_l_low_level_spec) (0)) = 0) ” 
  &&  “ (0 <= timer_v_low_level_spec) ” 
  &&  “ (timer_v_low_level_spec <= (count_nonzero (vis1_l_low_level_spec))) ”
  &&  (((radj_row_pre + (u_pre * sizeof(INT) ) )) # Int  |-> (Znth u_pre radj_row_l_low_level_spec 0))
  **  (IntArray.missing_i radj_row_pre u_pre 0 (n_pre + 1 ) radj_row_l_low_level_spec )
  **  (IntArray.full vis1_pre n_pre (replace_Znth (u_pre) (1) (vis1_l_low_level_spec)) )
  **  (IntArray.full radj_col_pre (m_of (radj_row_l_low_level_spec)) radj_col_l_low_level_spec )
  **  (IntArray.full fin_pre n_pre fin_l_low_level_spec )
  **  (IntArray.full timer_p_pre 1 (cons (timer_v_low_level_spec) ((@nil Z))) )
.

Definition dfs1_partial_solve_wit_3 := 
forall (timer_p_pre: Z) (fin_pre: Z) (vis1_pre: Z) (radj_row_pre: Z) (radj_col_pre: Z) (n_pre: Z) (u_pre: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (timer_v_low_level_spec: Z) (fin_l_low_level_spec: (@list Z)) (vis1_l_low_level_spec: (@list Z)) (radj_row_l_low_level_spec: (@list Z)) (radj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (PreH1 : (csr_wf1 g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_l_low_level_spec fin_l_low_level_spec )) (PreH2 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH3 : (safeExec (pre_dfs1 (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (vis1_l_low_level_spec) (fin_l_low_level_spec) (timer_v_low_level_spec)) (dfs_finish (g_low_level_spec) (u_pre)) X_low_level_spec )) (PreH4 : (0 <= u_pre)) (PreH5 : (u_pre < n_pre)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : ((Znth (u_pre) (vis1_l_low_level_spec) (0)) = 0)) (PreH8 : (0 <= timer_v_low_level_spec)) (PreH9 : (timer_v_low_level_spec <= (count_nonzero (vis1_l_low_level_spec)))) ,
  (IntArray.full radj_row_pre (n_pre + 1 ) radj_row_l_low_level_spec )
  **  (IntArray.full vis1_pre n_pre (replace_Znth (u_pre) (1) (vis1_l_low_level_spec)) )
  **  (IntArray.full radj_col_pre (m_of (radj_row_l_low_level_spec)) radj_col_l_low_level_spec )
  **  (IntArray.full fin_pre n_pre fin_l_low_level_spec )
  **  (IntArray.full timer_p_pre 1 (cons (timer_v_low_level_spec) ((@nil Z))) )
|--
  “ (csr_wf1 g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_l_low_level_spec fin_l_low_level_spec ) ” 
  &&  “ ((adj_verts (g_low_level_spec)) = n_pre) ” 
  &&  “ (safeExec (pre_dfs1 (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (vis1_l_low_level_spec) (fin_l_low_level_spec) (timer_v_low_level_spec)) (dfs_finish (g_low_level_spec) (u_pre)) X_low_level_spec ) ” 
  &&  “ (0 <= u_pre) ” 
  &&  “ (u_pre < n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ ((Znth (u_pre) (vis1_l_low_level_spec) (0)) = 0) ” 
  &&  “ (0 <= timer_v_low_level_spec) ” 
  &&  “ (timer_v_low_level_spec <= (count_nonzero (vis1_l_low_level_spec))) ”
  &&  (((radj_row_pre + ((u_pre + 1 ) * sizeof(INT) ) )) # Int  |-> (Znth (u_pre + 1 ) radj_row_l_low_level_spec 0))
  **  (IntArray.missing_i radj_row_pre (u_pre + 1 ) 0 (n_pre + 1 ) radj_row_l_low_level_spec )
  **  (IntArray.full vis1_pre n_pre (replace_Znth (u_pre) (1) (vis1_l_low_level_spec)) )
  **  (IntArray.full radj_col_pre (m_of (radj_row_l_low_level_spec)) radj_col_l_low_level_spec )
  **  (IntArray.full fin_pre n_pre fin_l_low_level_spec )
  **  (IntArray.full timer_p_pre 1 (cons (timer_v_low_level_spec) ((@nil Z))) )
.

Definition dfs1_partial_solve_wit_4 := 
forall (timer_p_pre: Z) (fin_pre: Z) (vis1_pre: Z) (radj_row_pre: Z) (radj_col_pre: Z) (n_pre: Z) (u_pre: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (timer_v_low_level_spec: Z) (vis1_l_low_level_spec: (@list Z)) (radj_row_l_low_level_spec: (@list Z)) (radj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (hi: Z) (lo: Z) (i: Z) (vis1_m: (@list Z)) (fin_m: (@list Z)) (timer_m: Z) (PreH1 : (i < hi)) (PreH2 : (csr_wf1 g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_m fin_m )) (PreH3 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH4 : (safeExec (pre_dfs1 (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (vis1_m) (fin_m) (timer_m)) (dfs_finish_from (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (u_pre) (i)) X_low_level_spec )) (PreH5 : (lo = (csr_lo (u_pre) (radj_row_l_low_level_spec)))) (PreH6 : (hi = (csr_hi (u_pre) (radj_row_l_low_level_spec)))) (PreH7 : (0 <= lo)) (PreH8 : (lo <= i)) (PreH9 : (i <= hi)) (PreH10 : (hi <= (m_of (radj_row_l_low_level_spec)))) (PreH11 : (0 <= u_pre)) (PreH12 : (u_pre < n_pre)) (PreH13 : (n_pre <= INT_MAX)) (PreH14 : (0 <= timer_m)) (PreH15 : (timer_m < (count_nonzero (vis1_m)))) (PreH16 : (((count_nonzero (vis1_m)) - timer_m ) = (((count_nonzero (vis1_l_low_level_spec)) - timer_v_low_level_spec ) + 1 ))) ,
  (IntArray.full radj_col_pre (m_of (radj_row_l_low_level_spec)) radj_col_l_low_level_spec )
  **  (IntArray.full radj_row_pre (n_pre + 1 ) radj_row_l_low_level_spec )
  **  (IntArray.full vis1_pre n_pre vis1_m )
  **  (IntArray.full fin_pre n_pre fin_m )
  **  (IntArray.full timer_p_pre 1 (cons (timer_m) ((@nil Z))) )
|--
  “ (i < hi) ” 
  &&  “ (csr_wf1 g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_m fin_m ) ” 
  &&  “ ((adj_verts (g_low_level_spec)) = n_pre) ” 
  &&  “ (safeExec (pre_dfs1 (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (vis1_m) (fin_m) (timer_m)) (dfs_finish_from (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (u_pre) (i)) X_low_level_spec ) ” 
  &&  “ (lo = (csr_lo (u_pre) (radj_row_l_low_level_spec))) ” 
  &&  “ (hi = (csr_hi (u_pre) (radj_row_l_low_level_spec))) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= i) ” 
  &&  “ (i <= hi) ” 
  &&  “ (hi <= (m_of (radj_row_l_low_level_spec))) ” 
  &&  “ (0 <= u_pre) ” 
  &&  “ (u_pre < n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (0 <= timer_m) ” 
  &&  “ (timer_m < (count_nonzero (vis1_m))) ” 
  &&  “ (((count_nonzero (vis1_m)) - timer_m ) = (((count_nonzero (vis1_l_low_level_spec)) - timer_v_low_level_spec ) + 1 )) ”
  &&  (((radj_col_pre + (i * sizeof(INT) ) )) # Int  |-> (Znth i radj_col_l_low_level_spec 0))
  **  (IntArray.missing_i radj_col_pre i 0 (m_of (radj_row_l_low_level_spec)) radj_col_l_low_level_spec )
  **  (IntArray.full radj_row_pre (n_pre + 1 ) radj_row_l_low_level_spec )
  **  (IntArray.full vis1_pre n_pre vis1_m )
  **  (IntArray.full fin_pre n_pre fin_m )
  **  (IntArray.full timer_p_pre 1 (cons (timer_m) ((@nil Z))) )
.

Definition dfs1_partial_solve_wit_5 := 
forall (timer_p_pre: Z) (fin_pre: Z) (vis1_pre: Z) (radj_row_pre: Z) (radj_col_pre: Z) (n_pre: Z) (u_pre: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (timer_v_low_level_spec: Z) (vis1_l_low_level_spec: (@list Z)) (radj_row_l_low_level_spec: (@list Z)) (radj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (vis1_m: (@list Z)) (fin_m: (@list Z)) (timer_m: Z) (i: Z) (lo: Z) (hi: Z) (v: Z) (PreH1 : (csr_wf1 g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_m fin_m )) (PreH2 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH3 : (safeExec (pre_dfs1 (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (vis1_m) (fin_m) (timer_m)) (dfs_finish_from (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (u_pre) (i)) X_low_level_spec )) (PreH4 : (lo = (csr_lo (u_pre) (radj_row_l_low_level_spec)))) (PreH5 : (hi = (csr_hi (u_pre) (radj_row_l_low_level_spec)))) (PreH6 : (0 <= lo)) (PreH7 : (lo <= i)) (PreH8 : (i < hi)) (PreH9 : (hi <= (m_of (radj_row_l_low_level_spec)))) (PreH10 : (0 <= u_pre)) (PreH11 : (u_pre < n_pre)) (PreH12 : (n_pre <= INT_MAX)) (PreH13 : (0 <= timer_m)) (PreH14 : (timer_m < (count_nonzero (vis1_m)))) (PreH15 : (((count_nonzero (vis1_m)) - timer_m ) = (((count_nonzero (vis1_l_low_level_spec)) - timer_v_low_level_spec ) + 1 ))) (PreH16 : (0 <= v)) (PreH17 : (v < n_pre)) (PreH18 : (v = (Znth (i) (radj_col_l_low_level_spec) (0)))) ,
  (IntArray.full radj_col_pre (m_of (radj_row_l_low_level_spec)) radj_col_l_low_level_spec )
  **  (IntArray.full radj_row_pre (n_pre + 1 ) radj_row_l_low_level_spec )
  **  (IntArray.full vis1_pre n_pre vis1_m )
  **  (IntArray.full fin_pre n_pre fin_m )
  **  (IntArray.full timer_p_pre 1 (cons (timer_m) ((@nil Z))) )
|--
  “ (csr_wf1 g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_m fin_m ) ” 
  &&  “ ((adj_verts (g_low_level_spec)) = n_pre) ” 
  &&  “ (safeExec (pre_dfs1 (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (vis1_m) (fin_m) (timer_m)) (dfs_finish_from (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (u_pre) (i)) X_low_level_spec ) ” 
  &&  “ (lo = (csr_lo (u_pre) (radj_row_l_low_level_spec))) ” 
  &&  “ (hi = (csr_hi (u_pre) (radj_row_l_low_level_spec))) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= i) ” 
  &&  “ (i < hi) ” 
  &&  “ (hi <= (m_of (radj_row_l_low_level_spec))) ” 
  &&  “ (0 <= u_pre) ” 
  &&  “ (u_pre < n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (0 <= timer_m) ” 
  &&  “ (timer_m < (count_nonzero (vis1_m))) ” 
  &&  “ (((count_nonzero (vis1_m)) - timer_m ) = (((count_nonzero (vis1_l_low_level_spec)) - timer_v_low_level_spec ) + 1 )) ” 
  &&  “ (0 <= v) ” 
  &&  “ (v < n_pre) ” 
  &&  “ (v = (Znth (i) (radj_col_l_low_level_spec) (0))) ”
  &&  (((vis1_pre + (v * sizeof(INT) ) )) # Int  |-> (Znth v vis1_m 0))
  **  (IntArray.missing_i vis1_pre v 0 n_pre vis1_m )
  **  (IntArray.full radj_col_pre (m_of (radj_row_l_low_level_spec)) radj_col_l_low_level_spec )
  **  (IntArray.full radj_row_pre (n_pre + 1 ) radj_row_l_low_level_spec )
  **  (IntArray.full fin_pre n_pre fin_m )
  **  (IntArray.full timer_p_pre 1 (cons (timer_m) ((@nil Z))) )
.

Definition dfs1_partial_solve_wit_6_pure := 
(
forall (timer_p_pre: Z) (fin_pre: Z) (vis1_pre: Z) (radj_row_pre: Z) (radj_col_pre: Z) (n_pre: Z) (u_pre: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (timer_v_low_level_spec: Z) (vis1_l_low_level_spec: (@list Z)) (radj_row_l_low_level_spec: (@list Z)) (radj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (vis1_m: (@list Z)) (fin_m: (@list Z)) (timer_m: Z) (i: Z) (lo: Z) (hi: Z) (v: Z) (PreH1 : ((Znth v vis1_m 0) = 0)) (PreH2 : (csr_wf1 g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_m fin_m )) (PreH3 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH4 : (safeExec (pre_dfs1 (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (vis1_m) (fin_m) (timer_m)) (dfs_finish_from (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (u_pre) (i)) X_low_level_spec )) (PreH5 : (lo = (csr_lo (u_pre) (radj_row_l_low_level_spec)))) (PreH6 : (hi = (csr_hi (u_pre) (radj_row_l_low_level_spec)))) (PreH7 : (0 <= lo)) (PreH8 : (lo <= i)) (PreH9 : (i < hi)) (PreH10 : (hi <= (m_of (radj_row_l_low_level_spec)))) (PreH11 : (0 <= u_pre)) (PreH12 : (u_pre < n_pre)) (PreH13 : (n_pre <= INT_MAX)) (PreH14 : (0 <= timer_m)) (PreH15 : (timer_m < (count_nonzero (vis1_m)))) (PreH16 : (((count_nonzero (vis1_m)) - timer_m ) = (((count_nonzero (vis1_l_low_level_spec)) - timer_v_low_level_spec ) + 1 ))) (PreH17 : (0 <= v)) (PreH18 : (v < n_pre)) (PreH19 : (v = (Znth (i) (radj_col_l_low_level_spec) (0)))) ,
  (IntArray.full vis1_pre n_pre vis1_m )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "u" ) )) # Int  |-> u_pre)
  **  ((( &( "radj_col" ) )) # Ptr  |-> radj_col_pre)
  **  ((( &( "radj_row" ) )) # Ptr  |-> radj_row_pre)
  **  ((( &( "vis1" ) )) # Ptr  |-> vis1_pre)
  **  ((( &( "fin" ) )) # Ptr  |-> fin_pre)
  **  ((( &( "timer_p" ) )) # Ptr  |-> timer_p_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  (IntArray.full radj_col_pre (m_of (radj_row_l_low_level_spec)) radj_col_l_low_level_spec )
  **  (IntArray.full radj_row_pre (n_pre + 1 ) radj_row_l_low_level_spec )
  **  (IntArray.full fin_pre n_pre fin_m )
  **  (IntArray.full timer_p_pre 1 (cons (timer_m) ((@nil Z))) )
|--
  “ (csr_wf1 g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_m fin_m ) ” 
  &&  “ ((adj_verts (g_low_level_spec)) = n_pre) ” 
  &&  “ (0 <= v) ” 
  &&  “ (v < n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (0 <= timer_m) ” 
  &&  “ (timer_m <= (count_nonzero (vis1_m))) ” 
  &&  “ ((Znth (v) (vis1_m) (0)) = 0) ” 
  &&  “ (safeExec (pre_dfs1 (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (vis1_m) (fin_m) (timer_m)) (bind ((dfs_finish (g_low_level_spec) (v))) ((dfs_finish_fromK (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (u_pre) ((i + 1 ))))) X_low_level_spec ) ”
) \/
(
forall (timer_p_pre: Z) (fin_pre: Z) (vis1_pre: Z) (radj_row_pre: Z) (radj_col_pre: Z) (n_pre: Z) (u_pre: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (timer_v_low_level_spec: Z) (vis1_l_low_level_spec: (@list Z)) (radj_row_l_low_level_spec: (@list Z)) (radj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (vis1_m: (@list Z)) (fin_m: (@list Z)) (timer_m: Z) (i: Z) (lo: Z) (hi: Z) (v: Z) (PreH1 : (v <= INT_MAX)) (PreH2 : (hi <= INT_MAX)) (PreH3 : (lo <= INT_MAX)) (PreH4 : (u_pre <= INT_MAX)) (PreH5 : (i <= INT_MAX)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : (v >= INT_MIN)) (PreH8 : (hi >= INT_MIN)) (PreH9 : (lo >= INT_MIN)) (PreH10 : (u_pre >= INT_MIN)) (PreH11 : (i >= INT_MIN)) (PreH12 : (n_pre >= INT_MIN)) (PreH13 : ((Znth v vis1_m 0) = 0)) (PreH14 : (csr_wf1 g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_m fin_m )) (PreH15 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH16 : (safeExec (pre_dfs1 (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (vis1_m) (fin_m) (timer_m)) (dfs_finish_from (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (u_pre) (i)) X_low_level_spec )) (PreH17 : (lo = (csr_lo (u_pre) (radj_row_l_low_level_spec)))) (PreH18 : (hi = (csr_hi (u_pre) (radj_row_l_low_level_spec)))) (PreH19 : (0 <= lo)) (PreH20 : (lo <= i)) (PreH21 : (i < hi)) (PreH22 : (hi <= (m_of (radj_row_l_low_level_spec)))) (PreH23 : (0 <= u_pre)) (PreH24 : (u_pre < n_pre)) (PreH25 : (n_pre <= INT_MAX)) (PreH26 : (0 <= timer_m)) (PreH27 : (timer_m < (count_nonzero (vis1_m)))) (PreH28 : (((count_nonzero (vis1_m)) - timer_m ) = (((count_nonzero (vis1_l_low_level_spec)) - timer_v_low_level_spec ) + 1 ))) (PreH29 : (0 <= v)) (PreH30 : (v < n_pre)) (PreH31 : (v = (Znth (i) (radj_col_l_low_level_spec) (0)))) ,
  (IntArray.full vis1_pre n_pre vis1_m )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "u" ) )) # Int  |-> u_pre)
  **  ((( &( "radj_col" ) )) # Ptr  |-> radj_col_pre)
  **  ((( &( "radj_row" ) )) # Ptr  |-> radj_row_pre)
  **  ((( &( "vis1" ) )) # Ptr  |-> vis1_pre)
  **  ((( &( "fin" ) )) # Ptr  |-> fin_pre)
  **  ((( &( "timer_p" ) )) # Ptr  |-> timer_p_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  (IntArray.full radj_col_pre (m_of (radj_row_l_low_level_spec)) radj_col_l_low_level_spec )
  **  (IntArray.full radj_row_pre (n_pre + 1 ) radj_row_l_low_level_spec )
  **  (IntArray.full fin_pre n_pre fin_m )
  **  (IntArray.full timer_p_pre 1 (cons (timer_m) ((@nil Z))) )
|--
  “ (safeExec (pre_dfs1 (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (vis1_m) (fin_m) (timer_m)) (bind ((dfs_finish (g_low_level_spec) (v))) ((dfs_finish_fromK (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (u_pre) ((i + 1 ))))) X_low_level_spec ) ” 
  &&  “ ((Znth (v) (vis1_m) (0)) = 0) ”
).

Definition dfs1_partial_solve_wit_6_pure_split_goal_1 := 
forall (timer_p_pre: Z) (fin_pre: Z) (vis1_pre: Z) (radj_row_pre: Z) (radj_col_pre: Z) (n_pre: Z) (u_pre: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (timer_v_low_level_spec: Z) (vis1_l_low_level_spec: (@list Z)) (radj_row_l_low_level_spec: (@list Z)) (radj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (vis1_m: (@list Z)) (fin_m: (@list Z)) (timer_m: Z) (i: Z) (lo: Z) (hi: Z) (v: Z) (PreH1 : (v <= INT_MAX)) (PreH2 : (hi <= INT_MAX)) (PreH3 : (lo <= INT_MAX)) (PreH4 : (u_pre <= INT_MAX)) (PreH5 : (i <= INT_MAX)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : (v >= INT_MIN)) (PreH8 : (hi >= INT_MIN)) (PreH9 : (lo >= INT_MIN)) (PreH10 : (u_pre >= INT_MIN)) (PreH11 : (i >= INT_MIN)) (PreH12 : (n_pre >= INT_MIN)) (PreH13 : ((Znth v vis1_m 0) = 0)) (PreH14 : (csr_wf1 g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_m fin_m )) (PreH15 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH16 : (safeExec (pre_dfs1 (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (vis1_m) (fin_m) (timer_m)) (dfs_finish_from (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (u_pre) (i)) X_low_level_spec )) (PreH17 : (lo = (csr_lo (u_pre) (radj_row_l_low_level_spec)))) (PreH18 : (hi = (csr_hi (u_pre) (radj_row_l_low_level_spec)))) (PreH19 : (0 <= lo)) (PreH20 : (lo <= i)) (PreH21 : (i < hi)) (PreH22 : (hi <= (m_of (radj_row_l_low_level_spec)))) (PreH23 : (0 <= u_pre)) (PreH24 : (u_pre < n_pre)) (PreH25 : (n_pre <= INT_MAX)) (PreH26 : (0 <= timer_m)) (PreH27 : (timer_m < (count_nonzero (vis1_m)))) (PreH28 : (((count_nonzero (vis1_m)) - timer_m ) = (((count_nonzero (vis1_l_low_level_spec)) - timer_v_low_level_spec ) + 1 ))) (PreH29 : (0 <= v)) (PreH30 : (v < n_pre)) (PreH31 : (v = (Znth (i) (radj_col_l_low_level_spec) (0)))) ,
  (IntArray.full vis1_pre n_pre vis1_m )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "u" ) )) # Int  |-> u_pre)
  **  ((( &( "radj_col" ) )) # Ptr  |-> radj_col_pre)
  **  ((( &( "radj_row" ) )) # Ptr  |-> radj_row_pre)
  **  ((( &( "vis1" ) )) # Ptr  |-> vis1_pre)
  **  ((( &( "fin" ) )) # Ptr  |-> fin_pre)
  **  ((( &( "timer_p" ) )) # Ptr  |-> timer_p_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  (IntArray.full radj_col_pre (m_of (radj_row_l_low_level_spec)) radj_col_l_low_level_spec )
  **  (IntArray.full radj_row_pre (n_pre + 1 ) radj_row_l_low_level_spec )
  **  (IntArray.full fin_pre n_pre fin_m )
  **  (IntArray.full timer_p_pre 1 (cons (timer_m) ((@nil Z))) )
|--
  “ (safeExec (pre_dfs1 (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (vis1_m) (fin_m) (timer_m)) (bind ((dfs_finish (g_low_level_spec) (v))) ((dfs_finish_fromK (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (u_pre) ((i + 1 ))))) X_low_level_spec ) ”
.

Definition dfs1_partial_solve_wit_6_pure_split_goal_2 := 
forall (timer_p_pre: Z) (fin_pre: Z) (vis1_pre: Z) (radj_row_pre: Z) (radj_col_pre: Z) (n_pre: Z) (u_pre: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (timer_v_low_level_spec: Z) (vis1_l_low_level_spec: (@list Z)) (radj_row_l_low_level_spec: (@list Z)) (radj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (vis1_m: (@list Z)) (fin_m: (@list Z)) (timer_m: Z) (i: Z) (lo: Z) (hi: Z) (v: Z) (PreH1 : (v <= INT_MAX)) (PreH2 : (hi <= INT_MAX)) (PreH3 : (lo <= INT_MAX)) (PreH4 : (u_pre <= INT_MAX)) (PreH5 : (i <= INT_MAX)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : (v >= INT_MIN)) (PreH8 : (hi >= INT_MIN)) (PreH9 : (lo >= INT_MIN)) (PreH10 : (u_pre >= INT_MIN)) (PreH11 : (i >= INT_MIN)) (PreH12 : (n_pre >= INT_MIN)) (PreH13 : ((Znth v vis1_m 0) = 0)) (PreH14 : (csr_wf1 g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_m fin_m )) (PreH15 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH16 : (safeExec (pre_dfs1 (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (vis1_m) (fin_m) (timer_m)) (dfs_finish_from (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (u_pre) (i)) X_low_level_spec )) (PreH17 : (lo = (csr_lo (u_pre) (radj_row_l_low_level_spec)))) (PreH18 : (hi = (csr_hi (u_pre) (radj_row_l_low_level_spec)))) (PreH19 : (0 <= lo)) (PreH20 : (lo <= i)) (PreH21 : (i < hi)) (PreH22 : (hi <= (m_of (radj_row_l_low_level_spec)))) (PreH23 : (0 <= u_pre)) (PreH24 : (u_pre < n_pre)) (PreH25 : (n_pre <= INT_MAX)) (PreH26 : (0 <= timer_m)) (PreH27 : (timer_m < (count_nonzero (vis1_m)))) (PreH28 : (((count_nonzero (vis1_m)) - timer_m ) = (((count_nonzero (vis1_l_low_level_spec)) - timer_v_low_level_spec ) + 1 ))) (PreH29 : (0 <= v)) (PreH30 : (v < n_pre)) (PreH31 : (v = (Znth (i) (radj_col_l_low_level_spec) (0)))) ,
  (IntArray.full vis1_pre n_pre vis1_m )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "u" ) )) # Int  |-> u_pre)
  **  ((( &( "radj_col" ) )) # Ptr  |-> radj_col_pre)
  **  ((( &( "radj_row" ) )) # Ptr  |-> radj_row_pre)
  **  ((( &( "vis1" ) )) # Ptr  |-> vis1_pre)
  **  ((( &( "fin" ) )) # Ptr  |-> fin_pre)
  **  ((( &( "timer_p" ) )) # Ptr  |-> timer_p_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  (IntArray.full radj_col_pre (m_of (radj_row_l_low_level_spec)) radj_col_l_low_level_spec )
  **  (IntArray.full radj_row_pre (n_pre + 1 ) radj_row_l_low_level_spec )
  **  (IntArray.full fin_pre n_pre fin_m )
  **  (IntArray.full timer_p_pre 1 (cons (timer_m) ((@nil Z))) )
|--
  “ ((Znth (v) (vis1_m) (0)) = 0) ”
.

Definition dfs1_partial_solve_wit_6_aux := 
forall (timer_p_pre: Z) (fin_pre: Z) (vis1_pre: Z) (radj_row_pre: Z) (radj_col_pre: Z) (n_pre: Z) (u_pre: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (timer_v_low_level_spec: Z) (vis1_l_low_level_spec: (@list Z)) (radj_row_l_low_level_spec: (@list Z)) (radj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (vis1_m: (@list Z)) (fin_m: (@list Z)) (timer_m: Z) (i: Z) (lo: Z) (hi: Z) (v: Z) (PreH1 : ((Znth v vis1_m 0) = 0)) (PreH2 : (csr_wf1 g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_m fin_m )) (PreH3 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH4 : (safeExec (pre_dfs1 (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (vis1_m) (fin_m) (timer_m)) (dfs_finish_from (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (u_pre) (i)) X_low_level_spec )) (PreH5 : (lo = (csr_lo (u_pre) (radj_row_l_low_level_spec)))) (PreH6 : (hi = (csr_hi (u_pre) (radj_row_l_low_level_spec)))) (PreH7 : (0 <= lo)) (PreH8 : (lo <= i)) (PreH9 : (i < hi)) (PreH10 : (hi <= (m_of (radj_row_l_low_level_spec)))) (PreH11 : (0 <= u_pre)) (PreH12 : (u_pre < n_pre)) (PreH13 : (n_pre <= INT_MAX)) (PreH14 : (0 <= timer_m)) (PreH15 : (timer_m < (count_nonzero (vis1_m)))) (PreH16 : (((count_nonzero (vis1_m)) - timer_m ) = (((count_nonzero (vis1_l_low_level_spec)) - timer_v_low_level_spec ) + 1 ))) (PreH17 : (0 <= v)) (PreH18 : (v < n_pre)) (PreH19 : (v = (Znth (i) (radj_col_l_low_level_spec) (0)))) ,
  (IntArray.full vis1_pre n_pre vis1_m )
  **  (IntArray.full radj_col_pre (m_of (radj_row_l_low_level_spec)) radj_col_l_low_level_spec )
  **  (IntArray.full radj_row_pre (n_pre + 1 ) radj_row_l_low_level_spec )
  **  (IntArray.full fin_pre n_pre fin_m )
  **  (IntArray.full timer_p_pre 1 (cons (timer_m) ((@nil Z))) )
|--
  “ (csr_wf1 g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_m fin_m ) ” 
  &&  “ ((adj_verts (g_low_level_spec)) = n_pre) ” 
  &&  “ (0 <= v) ” 
  &&  “ (v < n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (0 <= timer_m) ” 
  &&  “ (timer_m <= (count_nonzero (vis1_m))) ” 
  &&  “ ((Znth (v) (vis1_m) (0)) = 0) ” 
  &&  “ (safeExec (pre_dfs1 (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (vis1_m) (fin_m) (timer_m)) (bind ((dfs_finish (g_low_level_spec) (v))) ((dfs_finish_fromK (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (u_pre) ((i + 1 ))))) X_low_level_spec ) ” 
  &&  “ ((Znth v vis1_m 0) = 0) ” 
  &&  “ (csr_wf1 g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_m fin_m ) ” 
  &&  “ ((adj_verts (g_low_level_spec)) = n_pre) ” 
  &&  “ (safeExec (pre_dfs1 (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (vis1_m) (fin_m) (timer_m)) (dfs_finish_from (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (u_pre) (i)) X_low_level_spec ) ” 
  &&  “ (lo = (csr_lo (u_pre) (radj_row_l_low_level_spec))) ” 
  &&  “ (hi = (csr_hi (u_pre) (radj_row_l_low_level_spec))) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= i) ” 
  &&  “ (i < hi) ” 
  &&  “ (hi <= (m_of (radj_row_l_low_level_spec))) ” 
  &&  “ (0 <= u_pre) ” 
  &&  “ (u_pre < n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (0 <= timer_m) ” 
  &&  “ (timer_m < (count_nonzero (vis1_m))) ” 
  &&  “ (((count_nonzero (vis1_m)) - timer_m ) = (((count_nonzero (vis1_l_low_level_spec)) - timer_v_low_level_spec ) + 1 )) ” 
  &&  “ (0 <= v) ” 
  &&  “ (v < n_pre) ” 
  &&  “ (v = (Znth (i) (radj_col_l_low_level_spec) (0))) ”
  &&  (IntArray.full radj_col_pre (m_of (radj_row_l_low_level_spec)) radj_col_l_low_level_spec )
  **  (IntArray.full radj_row_pre (n_pre + 1 ) radj_row_l_low_level_spec )
  **  (IntArray.full vis1_pre n_pre vis1_m )
  **  (IntArray.full fin_pre n_pre fin_m )
  **  (IntArray.full timer_p_pre 1 (cons (timer_m) ((@nil Z))) )
.

Definition dfs1_partial_solve_wit_6 := dfs1_partial_solve_wit_6_pure -> dfs1_partial_solve_wit_6_aux.

Definition dfs1_partial_solve_wit_7 := 
forall (timer_p_pre: Z) (fin_pre: Z) (vis1_pre: Z) (radj_row_pre: Z) (radj_col_pre: Z) (n_pre: Z) (u_pre: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (timer_v_low_level_spec: Z) (vis1_l_low_level_spec: (@list Z)) (radj_row_l_low_level_spec: (@list Z)) (radj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (hi: Z) (lo: Z) (timer_m: Z) (i: Z) (vis1_m: (@list Z)) (fin_m: (@list Z)) (PreH1 : (i >= hi)) (PreH2 : (csr_wf1 g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_m fin_m )) (PreH3 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH4 : (safeExec (pre_dfs1 (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (vis1_m) (fin_m) (timer_m)) (dfs_finish_from (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (u_pre) (i)) X_low_level_spec )) (PreH5 : (lo = (csr_lo (u_pre) (radj_row_l_low_level_spec)))) (PreH6 : (hi = (csr_hi (u_pre) (radj_row_l_low_level_spec)))) (PreH7 : (0 <= lo)) (PreH8 : (lo <= i)) (PreH9 : (i <= hi)) (PreH10 : (hi <= (m_of (radj_row_l_low_level_spec)))) (PreH11 : (0 <= u_pre)) (PreH12 : (u_pre < n_pre)) (PreH13 : (n_pre <= INT_MAX)) (PreH14 : (0 <= timer_m)) (PreH15 : (timer_m < (count_nonzero (vis1_m)))) (PreH16 : (((count_nonzero (vis1_m)) - timer_m ) = (((count_nonzero (vis1_l_low_level_spec)) - timer_v_low_level_spec ) + 1 ))) ,
  (IntArray.full radj_col_pre (m_of (radj_row_l_low_level_spec)) radj_col_l_low_level_spec )
  **  (IntArray.full radj_row_pre (n_pre + 1 ) radj_row_l_low_level_spec )
  **  (IntArray.full vis1_pre n_pre vis1_m )
  **  (IntArray.full fin_pre n_pre fin_m )
  **  (IntArray.full timer_p_pre 1 (cons (timer_m) ((@nil Z))) )
|--
  “ (i >= hi) ” 
  &&  “ (csr_wf1 g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_m fin_m ) ” 
  &&  “ ((adj_verts (g_low_level_spec)) = n_pre) ” 
  &&  “ (safeExec (pre_dfs1 (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (vis1_m) (fin_m) (timer_m)) (dfs_finish_from (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (u_pre) (i)) X_low_level_spec ) ” 
  &&  “ (lo = (csr_lo (u_pre) (radj_row_l_low_level_spec))) ” 
  &&  “ (hi = (csr_hi (u_pre) (radj_row_l_low_level_spec))) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= i) ” 
  &&  “ (i <= hi) ” 
  &&  “ (hi <= (m_of (radj_row_l_low_level_spec))) ” 
  &&  “ (0 <= u_pre) ” 
  &&  “ (u_pre < n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (0 <= timer_m) ” 
  &&  “ (timer_m < (count_nonzero (vis1_m))) ” 
  &&  “ (((count_nonzero (vis1_m)) - timer_m ) = (((count_nonzero (vis1_l_low_level_spec)) - timer_v_low_level_spec ) + 1 )) ”
  &&  (((timer_p_pre + (0 * sizeof(INT) ) )) # Int  |-> (Znth 0 (cons (timer_m) ((@nil Z))) 0))
  **  (IntArray.missing_i timer_p_pre 0 0 1 (cons (timer_m) ((@nil Z))) )
  **  (IntArray.full radj_col_pre (m_of (radj_row_l_low_level_spec)) radj_col_l_low_level_spec )
  **  (IntArray.full radj_row_pre (n_pre + 1 ) radj_row_l_low_level_spec )
  **  (IntArray.full vis1_pre n_pre vis1_m )
  **  (IntArray.full fin_pre n_pre fin_m )
.

Definition dfs1_partial_solve_wit_8 := 
forall (timer_p_pre: Z) (fin_pre: Z) (vis1_pre: Z) (radj_row_pre: Z) (radj_col_pre: Z) (n_pre: Z) (u_pre: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (timer_v_low_level_spec: Z) (vis1_l_low_level_spec: (@list Z)) (radj_row_l_low_level_spec: (@list Z)) (radj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (hi: Z) (lo: Z) (timer_m: Z) (i: Z) (vis1_m: (@list Z)) (fin_m: (@list Z)) (PreH1 : (i >= hi)) (PreH2 : (csr_wf1 g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_m fin_m )) (PreH3 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH4 : (safeExec (pre_dfs1 (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (vis1_m) (fin_m) (timer_m)) (dfs_finish_from (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (u_pre) (i)) X_low_level_spec )) (PreH5 : (lo = (csr_lo (u_pre) (radj_row_l_low_level_spec)))) (PreH6 : (hi = (csr_hi (u_pre) (radj_row_l_low_level_spec)))) (PreH7 : (0 <= lo)) (PreH8 : (lo <= i)) (PreH9 : (i <= hi)) (PreH10 : (hi <= (m_of (radj_row_l_low_level_spec)))) (PreH11 : (0 <= u_pre)) (PreH12 : (u_pre < n_pre)) (PreH13 : (n_pre <= INT_MAX)) (PreH14 : (0 <= timer_m)) (PreH15 : (timer_m < (count_nonzero (vis1_m)))) (PreH16 : (((count_nonzero (vis1_m)) - timer_m ) = (((count_nonzero (vis1_l_low_level_spec)) - timer_v_low_level_spec ) + 1 ))) ,
  (IntArray.full timer_p_pre 1 (cons (timer_m) ((@nil Z))) )
  **  (IntArray.full radj_col_pre (m_of (radj_row_l_low_level_spec)) radj_col_l_low_level_spec )
  **  (IntArray.full radj_row_pre (n_pre + 1 ) radj_row_l_low_level_spec )
  **  (IntArray.full vis1_pre n_pre vis1_m )
  **  (IntArray.full fin_pre n_pre fin_m )
|--
  “ (i >= hi) ” 
  &&  “ (csr_wf1 g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_m fin_m ) ” 
  &&  “ ((adj_verts (g_low_level_spec)) = n_pre) ” 
  &&  “ (safeExec (pre_dfs1 (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (vis1_m) (fin_m) (timer_m)) (dfs_finish_from (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (u_pre) (i)) X_low_level_spec ) ” 
  &&  “ (lo = (csr_lo (u_pre) (radj_row_l_low_level_spec))) ” 
  &&  “ (hi = (csr_hi (u_pre) (radj_row_l_low_level_spec))) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= i) ” 
  &&  “ (i <= hi) ” 
  &&  “ (hi <= (m_of (radj_row_l_low_level_spec))) ” 
  &&  “ (0 <= u_pre) ” 
  &&  “ (u_pre < n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (0 <= timer_m) ” 
  &&  “ (timer_m < (count_nonzero (vis1_m))) ” 
  &&  “ (((count_nonzero (vis1_m)) - timer_m ) = (((count_nonzero (vis1_l_low_level_spec)) - timer_v_low_level_spec ) + 1 )) ”
  &&  (((fin_pre + (u_pre * sizeof(INT) ) )) # Int  |->_)
  **  (IntArray.missing_i fin_pre u_pre 0 n_pre fin_m )
  **  (IntArray.full timer_p_pre 1 (cons (timer_m) ((@nil Z))) )
  **  (IntArray.full radj_col_pre (m_of (radj_row_l_low_level_spec)) radj_col_l_low_level_spec )
  **  (IntArray.full radj_row_pre (n_pre + 1 ) radj_row_l_low_level_spec )
  **  (IntArray.full vis1_pre n_pre vis1_m )
.

Definition dfs1_partial_solve_wit_9 := 
forall (timer_p_pre: Z) (fin_pre: Z) (vis1_pre: Z) (radj_row_pre: Z) (radj_col_pre: Z) (n_pre: Z) (u_pre: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (timer_v_low_level_spec: Z) (vis1_l_low_level_spec: (@list Z)) (radj_row_l_low_level_spec: (@list Z)) (radj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (hi: Z) (lo: Z) (timer_m: Z) (i: Z) (vis1_m: (@list Z)) (fin_m: (@list Z)) (PreH1 : (i >= hi)) (PreH2 : (csr_wf1 g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_m fin_m )) (PreH3 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH4 : (safeExec (pre_dfs1 (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (vis1_m) (fin_m) (timer_m)) (dfs_finish_from (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (u_pre) (i)) X_low_level_spec )) (PreH5 : (lo = (csr_lo (u_pre) (radj_row_l_low_level_spec)))) (PreH6 : (hi = (csr_hi (u_pre) (radj_row_l_low_level_spec)))) (PreH7 : (0 <= lo)) (PreH8 : (lo <= i)) (PreH9 : (i <= hi)) (PreH10 : (hi <= (m_of (radj_row_l_low_level_spec)))) (PreH11 : (0 <= u_pre)) (PreH12 : (u_pre < n_pre)) (PreH13 : (n_pre <= INT_MAX)) (PreH14 : (0 <= timer_m)) (PreH15 : (timer_m < (count_nonzero (vis1_m)))) (PreH16 : (((count_nonzero (vis1_m)) - timer_m ) = (((count_nonzero (vis1_l_low_level_spec)) - timer_v_low_level_spec ) + 1 ))) ,
  (IntArray.full fin_pre n_pre (replace_Znth (u_pre) ((Znth 0 (cons (timer_m) ((@nil Z))) 0)) (fin_m)) )
  **  (IntArray.full timer_p_pre 1 (cons (timer_m) ((@nil Z))) )
  **  (IntArray.full radj_col_pre (m_of (radj_row_l_low_level_spec)) radj_col_l_low_level_spec )
  **  (IntArray.full radj_row_pre (n_pre + 1 ) radj_row_l_low_level_spec )
  **  (IntArray.full vis1_pre n_pre vis1_m )
|--
  “ (i >= hi) ” 
  &&  “ (csr_wf1 g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_m fin_m ) ” 
  &&  “ ((adj_verts (g_low_level_spec)) = n_pre) ” 
  &&  “ (safeExec (pre_dfs1 (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (vis1_m) (fin_m) (timer_m)) (dfs_finish_from (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (u_pre) (i)) X_low_level_spec ) ” 
  &&  “ (lo = (csr_lo (u_pre) (radj_row_l_low_level_spec))) ” 
  &&  “ (hi = (csr_hi (u_pre) (radj_row_l_low_level_spec))) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= i) ” 
  &&  “ (i <= hi) ” 
  &&  “ (hi <= (m_of (radj_row_l_low_level_spec))) ” 
  &&  “ (0 <= u_pre) ” 
  &&  “ (u_pre < n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (0 <= timer_m) ” 
  &&  “ (timer_m < (count_nonzero (vis1_m))) ” 
  &&  “ (((count_nonzero (vis1_m)) - timer_m ) = (((count_nonzero (vis1_l_low_level_spec)) - timer_v_low_level_spec ) + 1 )) ”
  &&  (((timer_p_pre + (0 * sizeof(INT) ) )) # Int  |->_)
  **  (IntArray.missing_i timer_p_pre 0 0 1 (cons (timer_m) ((@nil Z))) )
  **  (IntArray.full fin_pre n_pre (replace_Znth (u_pre) ((Znth 0 (cons (timer_m) ((@nil Z))) 0)) (fin_m)) )
  **  (IntArray.full radj_col_pre (m_of (radj_row_l_low_level_spec)) radj_col_l_low_level_spec )
  **  (IntArray.full radj_row_pre (n_pre + 1 ) radj_row_l_low_level_spec )
  **  (IntArray.full vis1_pre n_pre vis1_m )
.

(*----- Function dfs2 -----*)

Definition dfs2_safety_wit_1 := 
forall (sid_pre: Z) (vis2_pre: Z) (fadj_row_pre: Z) (fadj_col_pre: Z) (n_pre: Z) (u_pre: Z) (root_pre: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (root_v_low_level_spec: Z) (sid_l_low_level_spec: (@list Z)) (vis2_l_low_level_spec: (@list Z)) (fadj_row_l_low_level_spec: (@list Z)) (fadj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (PreH1 : (csr_wf2 g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec vis2_l_low_level_spec sid_l_low_level_spec )) (PreH2 : (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH3 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH4 : (safeExec (pre_dfs2 (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (vis2_l_low_level_spec) (sid_l_low_level_spec) (root_v_low_level_spec)) (dfs_scc (g_low_level_spec) (root_pre) (u_pre)) X_low_level_spec )) (PreH5 : (0 <= u_pre)) (PreH6 : (u_pre < n_pre)) (PreH7 : (0 <= root_pre)) (PreH8 : (root_pre < n_pre)) (PreH9 : (n_pre <= INT_MAX)) (PreH10 : ((Znth (root_pre) (vis2_l_low_level_spec) (0)) <> 0)) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "u" ) )) # Int  |-> u_pre)
  **  ((( &( "root" ) )) # Int  |-> root_pre)
  **  ((( &( "sid" ) )) # Ptr  |-> sid_pre)
  **  ((( &( "vis2" ) )) # Ptr  |-> vis2_pre)
  **  ((( &( "fadj_row" ) )) # Ptr  |-> fadj_row_pre)
  **  ((( &( "fadj_col" ) )) # Ptr  |-> fadj_col_pre)
  **  (IntArray.full fadj_col_pre (m_of (fadj_row_l_low_level_spec)) fadj_col_l_low_level_spec )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_low_level_spec )
  **  (IntArray.full vis2_pre n_pre vis2_l_low_level_spec )
  **  (IntArray.full sid_pre n_pre sid_l_low_level_spec )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition dfs2_safety_wit_2 := 
forall (sid_pre: Z) (vis2_pre: Z) (fadj_row_pre: Z) (fadj_col_pre: Z) (n_pre: Z) (u_pre: Z) (root_pre: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (root_v_low_level_spec: Z) (sid_l_low_level_spec: (@list Z)) (vis2_l_low_level_spec: (@list Z)) (fadj_row_l_low_level_spec: (@list Z)) (fadj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (PreH1 : (csr_wf2 g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec vis2_l_low_level_spec sid_l_low_level_spec )) (PreH2 : (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH3 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH4 : (safeExec (pre_dfs2 (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (vis2_l_low_level_spec) (sid_l_low_level_spec) (root_v_low_level_spec)) (dfs_scc (g_low_level_spec) (root_pre) (u_pre)) X_low_level_spec )) (PreH5 : (0 <= u_pre)) (PreH6 : (u_pre < n_pre)) (PreH7 : (0 <= root_pre)) (PreH8 : (root_pre < n_pre)) (PreH9 : (n_pre <= INT_MAX)) (PreH10 : ((Znth (root_pre) (vis2_l_low_level_spec) (0)) <> 0)) ,
  ((( &( "hi" ) )) # Int  |->_)
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_low_level_spec )
  **  ((( &( "lo" ) )) # Int  |-> (Znth u_pre fadj_row_l_low_level_spec 0))
  **  (IntArray.full sid_pre n_pre (replace_Znth (u_pre) ((Znth root_pre sid_l_low_level_spec 0)) (sid_l_low_level_spec)) )
  **  (IntArray.full vis2_pre n_pre (replace_Znth (u_pre) (1) (vis2_l_low_level_spec)) )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "u" ) )) # Int  |-> u_pre)
  **  ((( &( "root" ) )) # Int  |-> root_pre)
  **  ((( &( "sid" ) )) # Ptr  |-> sid_pre)
  **  ((( &( "vis2" ) )) # Ptr  |-> vis2_pre)
  **  ((( &( "fadj_row" ) )) # Ptr  |-> fadj_row_pre)
  **  ((( &( "fadj_col" ) )) # Ptr  |-> fadj_col_pre)
  **  (IntArray.full fadj_col_pre (m_of (fadj_row_l_low_level_spec)) fadj_col_l_low_level_spec )
|--
  “ ((u_pre + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (u_pre + 1 )) ”
.

Definition dfs2_safety_wit_3 := 
forall (sid_pre: Z) (vis2_pre: Z) (fadj_row_pre: Z) (fadj_col_pre: Z) (n_pre: Z) (u_pre: Z) (root_pre: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (root_v_low_level_spec: Z) (sid_l_low_level_spec: (@list Z)) (vis2_l_low_level_spec: (@list Z)) (fadj_row_l_low_level_spec: (@list Z)) (fadj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (PreH1 : (csr_wf2 g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec vis2_l_low_level_spec sid_l_low_level_spec )) (PreH2 : (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH3 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH4 : (safeExec (pre_dfs2 (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (vis2_l_low_level_spec) (sid_l_low_level_spec) (root_v_low_level_spec)) (dfs_scc (g_low_level_spec) (root_pre) (u_pre)) X_low_level_spec )) (PreH5 : (0 <= u_pre)) (PreH6 : (u_pre < n_pre)) (PreH7 : (0 <= root_pre)) (PreH8 : (root_pre < n_pre)) (PreH9 : (n_pre <= INT_MAX)) (PreH10 : ((Znth (root_pre) (vis2_l_low_level_spec) (0)) <> 0)) ,
  ((( &( "hi" ) )) # Int  |->_)
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_low_level_spec )
  **  ((( &( "lo" ) )) # Int  |-> (Znth u_pre fadj_row_l_low_level_spec 0))
  **  (IntArray.full sid_pre n_pre (replace_Znth (u_pre) ((Znth root_pre sid_l_low_level_spec 0)) (sid_l_low_level_spec)) )
  **  (IntArray.full vis2_pre n_pre (replace_Znth (u_pre) (1) (vis2_l_low_level_spec)) )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "u" ) )) # Int  |-> u_pre)
  **  ((( &( "root" ) )) # Int  |-> root_pre)
  **  ((( &( "sid" ) )) # Ptr  |-> sid_pre)
  **  ((( &( "vis2" ) )) # Ptr  |-> vis2_pre)
  **  ((( &( "fadj_row" ) )) # Ptr  |-> fadj_row_pre)
  **  ((( &( "fadj_col" ) )) # Ptr  |-> fadj_col_pre)
  **  (IntArray.full fadj_col_pre (m_of (fadj_row_l_low_level_spec)) fadj_col_l_low_level_spec )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition dfs2_safety_wit_4 := 
forall (sid_pre: Z) (vis2_pre: Z) (fadj_row_pre: Z) (fadj_col_pre: Z) (n_pre: Z) (u_pre: Z) (root_pre: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (root_v_low_level_spec: Z) (vis2_l_low_level_spec: (@list Z)) (fadj_row_l_low_level_spec: (@list Z)) (fadj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (vis2_m: (@list Z)) (sid_m: (@list Z)) (i: Z) (lo: Z) (hi: Z) (v: Z) (PreH1 : (csr_wf2 g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec vis2_m sid_m )) (PreH2 : (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH3 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH4 : (safeExec (pre_dfs2 (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (vis2_m) (sid_m) (root_v_low_level_spec)) (dfs_scc_from (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (root_pre) (u_pre) (i)) X_low_level_spec )) (PreH5 : (lo = (csr_lo (u_pre) (fadj_row_l_low_level_spec)))) (PreH6 : (hi = (csr_hi (u_pre) (fadj_row_l_low_level_spec)))) (PreH7 : (0 <= lo)) (PreH8 : (lo <= i)) (PreH9 : (i < hi)) (PreH10 : (hi <= (m_of (fadj_row_l_low_level_spec)))) (PreH11 : (0 <= u_pre)) (PreH12 : (u_pre < n_pre)) (PreH13 : (0 <= root_pre)) (PreH14 : (root_pre < n_pre)) (PreH15 : (n_pre <= INT_MAX)) (PreH16 : ((Znth (u_pre) (vis2_m) (0)) <> 0)) (PreH17 : forall (j: Z) , (((lo <= j) /\ (j < i)) -> ((Znth ((Znth (j) (fadj_col_l_low_level_spec) (0))) (vis2_m) (0)) <> 0))) (PreH18 : ((Znth (root_pre) (vis2_m) (0)) <> 0)) (PreH19 : forall (w: Z) , (((0 <= w) /\ (w < n_pre)) -> (((Znth (w) (vis2_l_low_level_spec) (0)) <> 0) -> ((Znth (w) (vis2_m) (0)) <> 0)))) (PreH20 : (0 <= v)) (PreH21 : (v < n_pre)) (PreH22 : (v = (Znth (i) (fadj_col_l_low_level_spec) (0)))) ,
  (IntArray.full vis2_pre n_pre vis2_m )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "u" ) )) # Int  |-> u_pre)
  **  ((( &( "root" ) )) # Int  |-> root_pre)
  **  ((( &( "fadj_col" ) )) # Ptr  |-> fadj_col_pre)
  **  ((( &( "fadj_row" ) )) # Ptr  |-> fadj_row_pre)
  **  ((( &( "vis2" ) )) # Ptr  |-> vis2_pre)
  **  ((( &( "sid" ) )) # Ptr  |-> sid_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  (IntArray.full fadj_col_pre (m_of (fadj_row_l_low_level_spec)) fadj_col_l_low_level_spec )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_low_level_spec )
  **  (IntArray.full sid_pre n_pre sid_m )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition dfs2_safety_wit_5 := 
forall (sid_pre: Z) (vis2_pre: Z) (fadj_row_pre: Z) (fadj_col_pre: Z) (n_pre: Z) (u_pre: Z) (root_pre: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (root_v_low_level_spec: Z) (vis2_l_low_level_spec: (@list Z)) (fadj_row_l_low_level_spec: (@list Z)) (fadj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (vis2_m: (@list Z)) (sid_m: (@list Z)) (i: Z) (lo: Z) (hi: Z) (v: Z) (vis2_l_: (@list Z)) (sid_l_: (@list Z)) (PreH1 : (csr_wf2 g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec vis2_l_ sid_l_ )) (PreH2 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH3 : (safeExec (pre_dfs2 (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (vis2_l_) (sid_l_) (root_v_low_level_spec)) (applyf ((dfs_scc_fromK (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (root_pre) (u_pre) ((i + 1 )))) (tt)) X_low_level_spec )) (PreH4 : ((Znth (v) (vis2_l_) (0)) <> 0)) (PreH5 : forall (w: Z) , (((0 <= w) /\ (w < n_pre)) -> (((Znth (w) (vis2_m) (0)) <> 0) -> ((Znth (w) (vis2_l_) (0)) <> 0)))) (PreH6 : ((Znth v vis2_m 0) = 0)) (PreH7 : (csr_wf2 g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec vis2_m sid_m )) (PreH8 : (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH9 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH10 : (lo = (csr_lo (u_pre) (fadj_row_l_low_level_spec)))) (PreH11 : (hi = (csr_hi (u_pre) (fadj_row_l_low_level_spec)))) (PreH12 : (0 <= lo)) (PreH13 : (lo <= i)) (PreH14 : (i < hi)) (PreH15 : (hi <= (m_of (fadj_row_l_low_level_spec)))) (PreH16 : (0 <= u_pre)) (PreH17 : (u_pre < n_pre)) (PreH18 : (0 <= root_pre)) (PreH19 : (root_pre < n_pre)) (PreH20 : (n_pre <= INT_MAX)) (PreH21 : ((Znth (u_pre) (vis2_m) (0)) <> 0)) (PreH22 : forall (j: Z) , (((lo <= j) /\ (j < i)) -> ((Znth ((Znth (j) (fadj_col_l_low_level_spec) (0))) (vis2_m) (0)) <> 0))) (PreH23 : ((Znth (root_pre) (vis2_m) (0)) <> 0)) (PreH24 : forall (w_2: Z) , (((0 <= w_2) /\ (w_2 < n_pre)) -> (((Znth (w_2) (vis2_l_low_level_spec) (0)) <> 0) -> ((Znth (w_2) (vis2_m) (0)) <> 0)))) (PreH25 : (0 <= v)) (PreH26 : (v < n_pre)) (PreH27 : (v = (Znth (i) (fadj_col_l_low_level_spec) (0)))) ,
  (IntArray.full fadj_col_pre (m_of (fadj_row_l_low_level_spec)) fadj_col_l_low_level_spec )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_low_level_spec )
  **  (IntArray.full vis2_pre n_pre vis2_l_ )
  **  (IntArray.full sid_pre n_pre sid_l_ )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "u" ) )) # Int  |-> u_pre)
  **  ((( &( "root" ) )) # Int  |-> root_pre)
  **  ((( &( "fadj_col" ) )) # Ptr  |-> fadj_col_pre)
  **  ((( &( "fadj_row" ) )) # Ptr  |-> fadj_row_pre)
  **  ((( &( "vis2" ) )) # Ptr  |-> vis2_pre)
  **  ((( &( "sid" ) )) # Ptr  |-> sid_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "v" ) )) # Int  |-> v)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition dfs2_safety_wit_6 := 
forall (sid_pre: Z) (vis2_pre: Z) (fadj_row_pre: Z) (fadj_col_pre: Z) (n_pre: Z) (u_pre: Z) (root_pre: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (root_v_low_level_spec: Z) (vis2_l_low_level_spec: (@list Z)) (fadj_row_l_low_level_spec: (@list Z)) (fadj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (vis2_m: (@list Z)) (sid_m: (@list Z)) (i: Z) (lo: Z) (hi: Z) (v: Z) (vis2_l_: (@list Z)) (sid_l_: (@list Z)) (PreH1 : (csr_wf2 g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec vis2_l_ sid_l_ )) (PreH2 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH3 : (safeExec (pre_dfs2 (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (vis2_l_) (sid_l_) (root_v_low_level_spec)) (applyf ((dfs_scc_fromK (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (root_pre) (u_pre) ((i + 1 )))) (tt)) X_low_level_spec )) (PreH4 : ((Znth (v) (vis2_l_) (0)) <> 0)) (PreH5 : forall (w: Z) , (((0 <= w) /\ (w < n_pre)) -> (((Znth (w) (vis2_m) (0)) <> 0) -> ((Znth (w) (vis2_l_) (0)) <> 0)))) (PreH6 : ((Znth v vis2_m 0) = 0)) (PreH7 : (csr_wf2 g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec vis2_m sid_m )) (PreH8 : (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH9 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH10 : (lo = (csr_lo (u_pre) (fadj_row_l_low_level_spec)))) (PreH11 : (hi = (csr_hi (u_pre) (fadj_row_l_low_level_spec)))) (PreH12 : (0 <= lo)) (PreH13 : (lo <= i)) (PreH14 : (i < hi)) (PreH15 : (hi <= (m_of (fadj_row_l_low_level_spec)))) (PreH16 : (0 <= u_pre)) (PreH17 : (u_pre < n_pre)) (PreH18 : (0 <= root_pre)) (PreH19 : (root_pre < n_pre)) (PreH20 : (n_pre <= INT_MAX)) (PreH21 : ((Znth (u_pre) (vis2_m) (0)) <> 0)) (PreH22 : forall (j: Z) , (((lo <= j) /\ (j < i)) -> ((Znth ((Znth (j) (fadj_col_l_low_level_spec) (0))) (vis2_m) (0)) <> 0))) (PreH23 : ((Znth (root_pre) (vis2_m) (0)) <> 0)) (PreH24 : forall (w_2: Z) , (((0 <= w_2) /\ (w_2 < n_pre)) -> (((Znth (w_2) (vis2_l_low_level_spec) (0)) <> 0) -> ((Znth (w_2) (vis2_m) (0)) <> 0)))) (PreH25 : (0 <= v)) (PreH26 : (v < n_pre)) (PreH27 : (v = (Znth (i) (fadj_col_l_low_level_spec) (0)))) ,
  (IntArray.full fadj_col_pre (m_of (fadj_row_l_low_level_spec)) fadj_col_l_low_level_spec )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_low_level_spec )
  **  (IntArray.full vis2_pre n_pre vis2_l_ )
  **  (IntArray.full sid_pre n_pre sid_l_ )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "u" ) )) # Int  |-> u_pre)
  **  ((( &( "root" ) )) # Int  |-> root_pre)
  **  ((( &( "fadj_col" ) )) # Ptr  |-> fadj_col_pre)
  **  ((( &( "fadj_row" ) )) # Ptr  |-> fadj_row_pre)
  **  ((( &( "vis2" ) )) # Ptr  |-> vis2_pre)
  **  ((( &( "sid" ) )) # Ptr  |-> sid_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "v" ) )) # Int  |-> v)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition dfs2_safety_wit_7 := 
forall (sid_pre: Z) (vis2_pre: Z) (fadj_row_pre: Z) (fadj_col_pre: Z) (n_pre: Z) (u_pre: Z) (root_pre: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (root_v_low_level_spec: Z) (vis2_l_low_level_spec: (@list Z)) (fadj_row_l_low_level_spec: (@list Z)) (fadj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (vis2_m: (@list Z)) (sid_m: (@list Z)) (i: Z) (lo: Z) (hi: Z) (v: Z) (PreH1 : ((Znth v vis2_m 0) <> 0)) (PreH2 : (csr_wf2 g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec vis2_m sid_m )) (PreH3 : (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH4 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH5 : (safeExec (pre_dfs2 (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (vis2_m) (sid_m) (root_v_low_level_spec)) (dfs_scc_from (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (root_pre) (u_pre) (i)) X_low_level_spec )) (PreH6 : (lo = (csr_lo (u_pre) (fadj_row_l_low_level_spec)))) (PreH7 : (hi = (csr_hi (u_pre) (fadj_row_l_low_level_spec)))) (PreH8 : (0 <= lo)) (PreH9 : (lo <= i)) (PreH10 : (i < hi)) (PreH11 : (hi <= (m_of (fadj_row_l_low_level_spec)))) (PreH12 : (0 <= u_pre)) (PreH13 : (u_pre < n_pre)) (PreH14 : (0 <= root_pre)) (PreH15 : (root_pre < n_pre)) (PreH16 : (n_pre <= INT_MAX)) (PreH17 : ((Znth (u_pre) (vis2_m) (0)) <> 0)) (PreH18 : forall (j: Z) , (((lo <= j) /\ (j < i)) -> ((Znth ((Znth (j) (fadj_col_l_low_level_spec) (0))) (vis2_m) (0)) <> 0))) (PreH19 : ((Znth (root_pre) (vis2_m) (0)) <> 0)) (PreH20 : forall (w: Z) , (((0 <= w) /\ (w < n_pre)) -> (((Znth (w) (vis2_l_low_level_spec) (0)) <> 0) -> ((Znth (w) (vis2_m) (0)) <> 0)))) (PreH21 : (0 <= v)) (PreH22 : (v < n_pre)) (PreH23 : (v = (Znth (i) (fadj_col_l_low_level_spec) (0)))) ,
  (IntArray.full vis2_pre n_pre vis2_m )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "u" ) )) # Int  |-> u_pre)
  **  ((( &( "root" ) )) # Int  |-> root_pre)
  **  ((( &( "fadj_col" ) )) # Ptr  |-> fadj_col_pre)
  **  ((( &( "fadj_row" ) )) # Ptr  |-> fadj_row_pre)
  **  ((( &( "vis2" ) )) # Ptr  |-> vis2_pre)
  **  ((( &( "sid" ) )) # Ptr  |-> sid_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  (IntArray.full fadj_col_pre (m_of (fadj_row_l_low_level_spec)) fadj_col_l_low_level_spec )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_low_level_spec )
  **  (IntArray.full sid_pre n_pre sid_m )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition dfs2_safety_wit_8 := 
forall (sid_pre: Z) (vis2_pre: Z) (fadj_row_pre: Z) (fadj_col_pre: Z) (n_pre: Z) (u_pre: Z) (root_pre: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (root_v_low_level_spec: Z) (vis2_l_low_level_spec: (@list Z)) (fadj_row_l_low_level_spec: (@list Z)) (fadj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (vis2_m: (@list Z)) (sid_m: (@list Z)) (i: Z) (lo: Z) (hi: Z) (v: Z) (PreH1 : ((Znth v vis2_m 0) <> 0)) (PreH2 : (csr_wf2 g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec vis2_m sid_m )) (PreH3 : (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH4 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH5 : (safeExec (pre_dfs2 (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (vis2_m) (sid_m) (root_v_low_level_spec)) (dfs_scc_from (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (root_pre) (u_pre) (i)) X_low_level_spec )) (PreH6 : (lo = (csr_lo (u_pre) (fadj_row_l_low_level_spec)))) (PreH7 : (hi = (csr_hi (u_pre) (fadj_row_l_low_level_spec)))) (PreH8 : (0 <= lo)) (PreH9 : (lo <= i)) (PreH10 : (i < hi)) (PreH11 : (hi <= (m_of (fadj_row_l_low_level_spec)))) (PreH12 : (0 <= u_pre)) (PreH13 : (u_pre < n_pre)) (PreH14 : (0 <= root_pre)) (PreH15 : (root_pre < n_pre)) (PreH16 : (n_pre <= INT_MAX)) (PreH17 : ((Znth (u_pre) (vis2_m) (0)) <> 0)) (PreH18 : forall (j: Z) , (((lo <= j) /\ (j < i)) -> ((Znth ((Znth (j) (fadj_col_l_low_level_spec) (0))) (vis2_m) (0)) <> 0))) (PreH19 : ((Znth (root_pre) (vis2_m) (0)) <> 0)) (PreH20 : forall (w: Z) , (((0 <= w) /\ (w < n_pre)) -> (((Znth (w) (vis2_l_low_level_spec) (0)) <> 0) -> ((Znth (w) (vis2_m) (0)) <> 0)))) (PreH21 : (0 <= v)) (PreH22 : (v < n_pre)) (PreH23 : (v = (Znth (i) (fadj_col_l_low_level_spec) (0)))) ,
  (IntArray.full vis2_pre n_pre vis2_m )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "u" ) )) # Int  |-> u_pre)
  **  ((( &( "root" ) )) # Int  |-> root_pre)
  **  ((( &( "fadj_col" ) )) # Ptr  |-> fadj_col_pre)
  **  ((( &( "fadj_row" ) )) # Ptr  |-> fadj_row_pre)
  **  ((( &( "vis2" ) )) # Ptr  |-> vis2_pre)
  **  ((( &( "sid" ) )) # Ptr  |-> sid_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  (IntArray.full fadj_col_pre (m_of (fadj_row_l_low_level_spec)) fadj_col_l_low_level_spec )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_low_level_spec )
  **  (IntArray.full sid_pre n_pre sid_m )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition dfs2_entail_wit_1 := 
(
forall (sid_pre: Z) (vis2_pre: Z) (fadj_row_pre: Z) (fadj_col_pre: Z) (n_pre: Z) (u_pre: Z) (root_pre: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (root_v_low_level_spec: Z) (sid_l_low_level_spec: (@list Z)) (vis2_l_low_level_spec: (@list Z)) (fadj_row_l_low_level_spec: (@list Z)) (fadj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (PreH1 : (csr_wf2 g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec vis2_l_low_level_spec sid_l_low_level_spec )) (PreH2 : (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH3 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH4 : (safeExec (pre_dfs2 (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (vis2_l_low_level_spec) (sid_l_low_level_spec) (root_v_low_level_spec)) (dfs_scc (g_low_level_spec) (root_pre) (u_pre)) X_low_level_spec )) (PreH5 : (0 <= u_pre)) (PreH6 : (u_pre < n_pre)) (PreH7 : (0 <= root_pre)) (PreH8 : (root_pre < n_pre)) (PreH9 : (n_pre <= INT_MAX)) (PreH10 : ((Znth (root_pre) (vis2_l_low_level_spec) (0)) <> 0)) ,
  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_low_level_spec )
  **  (IntArray.full sid_pre n_pre (replace_Znth (u_pre) ((Znth root_pre sid_l_low_level_spec 0)) (sid_l_low_level_spec)) )
  **  (IntArray.full vis2_pre n_pre (replace_Znth (u_pre) (1) (vis2_l_low_level_spec)) )
  **  (IntArray.full fadj_col_pre (m_of (fadj_row_l_low_level_spec)) fadj_col_l_low_level_spec )
|--
  EX (vis2_m: (@list Z))  (sid_m: (@list Z)) ,
  “ (csr_wf2 g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec vis2_m sid_m ) ” 
  &&  “ (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec ) ” 
  &&  “ ((adj_verts (g_low_level_spec)) = n_pre) ” 
  &&  “ (safeExec (pre_dfs2 (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (vis2_m) (sid_m) (root_v_low_level_spec)) (dfs_scc_from (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (root_pre) (u_pre) ((Znth u_pre fadj_row_l_low_level_spec 0))) X_low_level_spec ) ” 
  &&  “ ((Znth u_pre fadj_row_l_low_level_spec 0) = (csr_lo (u_pre) (fadj_row_l_low_level_spec))) ” 
  &&  “ ((Znth (u_pre + 1 ) fadj_row_l_low_level_spec 0) = (csr_hi (u_pre) (fadj_row_l_low_level_spec))) ” 
  &&  “ (0 <= (Znth u_pre fadj_row_l_low_level_spec 0)) ” 
  &&  “ ((Znth u_pre fadj_row_l_low_level_spec 0) <= (Znth u_pre fadj_row_l_low_level_spec 0)) ” 
  &&  “ ((Znth u_pre fadj_row_l_low_level_spec 0) <= (Znth (u_pre + 1 ) fadj_row_l_low_level_spec 0)) ” 
  &&  “ ((Znth (u_pre + 1 ) fadj_row_l_low_level_spec 0) <= (m_of (fadj_row_l_low_level_spec))) ” 
  &&  “ (0 <= u_pre) ” 
  &&  “ (u_pre < n_pre) ” 
  &&  “ (0 <= root_pre) ” 
  &&  “ (root_pre < n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ ((Znth (u_pre) (vis2_m) (0)) <> 0) ” 
  &&  “ forall (j: Z) , ((((Znth u_pre fadj_row_l_low_level_spec 0) <= j) /\ (j < (Znth u_pre fadj_row_l_low_level_spec 0))) -> ((Znth ((Znth (j) (fadj_col_l_low_level_spec) (0))) (vis2_m) (0)) <> 0)) ” 
  &&  “ ((Znth (root_pre) (vis2_m) (0)) <> 0) ” 
  &&  “ forall (w: Z) , (((0 <= w) /\ (w < n_pre)) -> (((Znth (w) (vis2_l_low_level_spec) (0)) <> 0) -> ((Znth (w) (vis2_m) (0)) <> 0))) ”
  &&  (IntArray.full fadj_col_pre (m_of (fadj_row_l_low_level_spec)) fadj_col_l_low_level_spec )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_low_level_spec )
  **  (IntArray.full vis2_pre n_pre vis2_m )
  **  (IntArray.full sid_pre n_pre sid_m )
) \/
(
forall (n_pre: Z) (u_pre: Z) (root_pre: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (root_v_low_level_spec: Z) (sid_l_low_level_spec: (@list Z)) (vis2_l_low_level_spec: (@list Z)) (fadj_row_l_low_level_spec: (@list Z)) (fadj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (PreH1 : (csr_wf2 g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec vis2_l_low_level_spec sid_l_low_level_spec )) (PreH2 : (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH3 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH4 : (safeExec (pre_dfs2 (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (vis2_l_low_level_spec) (sid_l_low_level_spec) (root_v_low_level_spec)) (dfs_scc (g_low_level_spec) (root_pre) (u_pre)) X_low_level_spec )) (PreH5 : (0 <= u_pre)) (PreH6 : (u_pre < n_pre)) (PreH7 : (0 <= root_pre)) (PreH8 : (root_pre < n_pre)) (PreH9 : (n_pre <= INT_MAX)) (PreH10 : ((Znth (root_pre) (vis2_l_low_level_spec) (0)) <> 0)) ,
  TT && emp 
|--
  “ ((((Znth (0) (vis2_l_low_level_spec) (0)) <> 0) -> ((Znth (0) ((replace_Znth (u_pre) (1) (vis2_l_low_level_spec))) (0)) <> 0)) /\ (((Znth ((n_pre - 1 )) (vis2_l_low_level_spec) (0)) <> 0) -> ((Znth ((n_pre - 1 )) ((replace_Znth (u_pre) (1) (vis2_l_low_level_spec))) (0)) <> 0))) ” 
  &&  “ ((Znth (root_pre) ((replace_Znth (u_pre) (1) (vis2_l_low_level_spec))) (0)) <> 0) ” 
  &&  “ ((Znth (u_pre) ((replace_Znth (u_pre) (1) (vis2_l_low_level_spec))) (0)) <> 0) ” 
  &&  “ ((Znth (u_pre + 1 ) fadj_row_l_low_level_spec 0) <= (m_of (fadj_row_l_low_level_spec))) ” 
  &&  “ ((Znth u_pre fadj_row_l_low_level_spec 0) <= (Znth (u_pre + 1 ) fadj_row_l_low_level_spec 0)) ” 
  &&  “ (0 <= (Znth u_pre fadj_row_l_low_level_spec 0)) ” 
  &&  “ ((Znth (u_pre + 1 ) fadj_row_l_low_level_spec 0) = (csr_hi (u_pre) (fadj_row_l_low_level_spec))) ” 
  &&  “ ((Znth u_pre fadj_row_l_low_level_spec 0) = (csr_lo (u_pre) (fadj_row_l_low_level_spec))) ” 
  &&  “ (safeExec (pre_dfs2 (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) ((replace_Znth (u_pre) (1) (vis2_l_low_level_spec))) ((replace_Znth (u_pre) ((Znth root_pre sid_l_low_level_spec 0)) (sid_l_low_level_spec))) (root_v_low_level_spec)) (dfs_scc_from (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (root_pre) (u_pre) ((Znth u_pre fadj_row_l_low_level_spec 0))) X_low_level_spec ) ” 
  &&  “ (csr_wf2 g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec (replace_Znth (u_pre) (1) (vis2_l_low_level_spec)) (replace_Znth (u_pre) ((Znth root_pre sid_l_low_level_spec 0)) (sid_l_low_level_spec)) ) ”
  &&  emp
).

Definition dfs2_entail_wit_1_split_goal_1 := 
forall (n_pre: Z) (u_pre: Z) (root_pre: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (root_v_low_level_spec: Z) (sid_l_low_level_spec: (@list Z)) (vis2_l_low_level_spec: (@list Z)) (fadj_row_l_low_level_spec: (@list Z)) (fadj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (PreH1 : (csr_wf2 g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec vis2_l_low_level_spec sid_l_low_level_spec )) (PreH2 : (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH3 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH4 : (safeExec (pre_dfs2 (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (vis2_l_low_level_spec) (sid_l_low_level_spec) (root_v_low_level_spec)) (dfs_scc (g_low_level_spec) (root_pre) (u_pre)) X_low_level_spec )) (PreH5 : (0 <= u_pre)) (PreH6 : (u_pre < n_pre)) (PreH7 : (0 <= root_pre)) (PreH8 : (root_pre < n_pre)) (PreH9 : (n_pre <= INT_MAX)) (PreH10 : ((Znth (root_pre) (vis2_l_low_level_spec) (0)) <> 0)) ,
  TT && emp 
|--
  “ ((((Znth (0) (vis2_l_low_level_spec) (0)) <> 0) -> ((Znth (0) ((replace_Znth (u_pre) (1) (vis2_l_low_level_spec))) (0)) <> 0)) /\ (((Znth ((n_pre - 1 )) (vis2_l_low_level_spec) (0)) <> 0) -> ((Znth ((n_pre - 1 )) ((replace_Znth (u_pre) (1) (vis2_l_low_level_spec))) (0)) <> 0))) ”
.

Definition dfs2_entail_wit_1_split_goal_2 := 
forall (n_pre: Z) (u_pre: Z) (root_pre: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (root_v_low_level_spec: Z) (sid_l_low_level_spec: (@list Z)) (vis2_l_low_level_spec: (@list Z)) (fadj_row_l_low_level_spec: (@list Z)) (fadj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (PreH1 : (csr_wf2 g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec vis2_l_low_level_spec sid_l_low_level_spec )) (PreH2 : (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH3 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH4 : (safeExec (pre_dfs2 (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (vis2_l_low_level_spec) (sid_l_low_level_spec) (root_v_low_level_spec)) (dfs_scc (g_low_level_spec) (root_pre) (u_pre)) X_low_level_spec )) (PreH5 : (0 <= u_pre)) (PreH6 : (u_pre < n_pre)) (PreH7 : (0 <= root_pre)) (PreH8 : (root_pre < n_pre)) (PreH9 : (n_pre <= INT_MAX)) (PreH10 : ((Znth (root_pre) (vis2_l_low_level_spec) (0)) <> 0)) ,
  TT && emp 
|--
  “ ((Znth (root_pre) ((replace_Znth (u_pre) (1) (vis2_l_low_level_spec))) (0)) <> 0) ”
.

Definition dfs2_entail_wit_1_split_goal_3 := 
forall (n_pre: Z) (u_pre: Z) (root_pre: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (root_v_low_level_spec: Z) (sid_l_low_level_spec: (@list Z)) (vis2_l_low_level_spec: (@list Z)) (fadj_row_l_low_level_spec: (@list Z)) (fadj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (PreH1 : (csr_wf2 g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec vis2_l_low_level_spec sid_l_low_level_spec )) (PreH2 : (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH3 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH4 : (safeExec (pre_dfs2 (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (vis2_l_low_level_spec) (sid_l_low_level_spec) (root_v_low_level_spec)) (dfs_scc (g_low_level_spec) (root_pre) (u_pre)) X_low_level_spec )) (PreH5 : (0 <= u_pre)) (PreH6 : (u_pre < n_pre)) (PreH7 : (0 <= root_pre)) (PreH8 : (root_pre < n_pre)) (PreH9 : (n_pre <= INT_MAX)) (PreH10 : ((Znth (root_pre) (vis2_l_low_level_spec) (0)) <> 0)) ,
  TT && emp 
|--
  “ ((Znth (u_pre) ((replace_Znth (u_pre) (1) (vis2_l_low_level_spec))) (0)) <> 0) ”
.

Definition dfs2_entail_wit_1_split_goal_4 := 
forall (n_pre: Z) (u_pre: Z) (root_pre: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (root_v_low_level_spec: Z) (sid_l_low_level_spec: (@list Z)) (vis2_l_low_level_spec: (@list Z)) (fadj_row_l_low_level_spec: (@list Z)) (fadj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (PreH1 : (csr_wf2 g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec vis2_l_low_level_spec sid_l_low_level_spec )) (PreH2 : (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH3 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH4 : (safeExec (pre_dfs2 (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (vis2_l_low_level_spec) (sid_l_low_level_spec) (root_v_low_level_spec)) (dfs_scc (g_low_level_spec) (root_pre) (u_pre)) X_low_level_spec )) (PreH5 : (0 <= u_pre)) (PreH6 : (u_pre < n_pre)) (PreH7 : (0 <= root_pre)) (PreH8 : (root_pre < n_pre)) (PreH9 : (n_pre <= INT_MAX)) (PreH10 : ((Znth (root_pre) (vis2_l_low_level_spec) (0)) <> 0)) ,
  TT && emp 
|--
  “ ((Znth (u_pre + 1 ) fadj_row_l_low_level_spec 0) <= (m_of (fadj_row_l_low_level_spec))) ”
.

Definition dfs2_entail_wit_1_split_goal_5 := 
forall (n_pre: Z) (u_pre: Z) (root_pre: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (root_v_low_level_spec: Z) (sid_l_low_level_spec: (@list Z)) (vis2_l_low_level_spec: (@list Z)) (fadj_row_l_low_level_spec: (@list Z)) (fadj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (PreH1 : (csr_wf2 g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec vis2_l_low_level_spec sid_l_low_level_spec )) (PreH2 : (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH3 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH4 : (safeExec (pre_dfs2 (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (vis2_l_low_level_spec) (sid_l_low_level_spec) (root_v_low_level_spec)) (dfs_scc (g_low_level_spec) (root_pre) (u_pre)) X_low_level_spec )) (PreH5 : (0 <= u_pre)) (PreH6 : (u_pre < n_pre)) (PreH7 : (0 <= root_pre)) (PreH8 : (root_pre < n_pre)) (PreH9 : (n_pre <= INT_MAX)) (PreH10 : ((Znth (root_pre) (vis2_l_low_level_spec) (0)) <> 0)) ,
  TT && emp 
|--
  “ ((Znth u_pre fadj_row_l_low_level_spec 0) <= (Znth (u_pre + 1 ) fadj_row_l_low_level_spec 0)) ”
.

Definition dfs2_entail_wit_1_split_goal_6 := 
forall (n_pre: Z) (u_pre: Z) (root_pre: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (root_v_low_level_spec: Z) (sid_l_low_level_spec: (@list Z)) (vis2_l_low_level_spec: (@list Z)) (fadj_row_l_low_level_spec: (@list Z)) (fadj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (PreH1 : (csr_wf2 g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec vis2_l_low_level_spec sid_l_low_level_spec )) (PreH2 : (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH3 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH4 : (safeExec (pre_dfs2 (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (vis2_l_low_level_spec) (sid_l_low_level_spec) (root_v_low_level_spec)) (dfs_scc (g_low_level_spec) (root_pre) (u_pre)) X_low_level_spec )) (PreH5 : (0 <= u_pre)) (PreH6 : (u_pre < n_pre)) (PreH7 : (0 <= root_pre)) (PreH8 : (root_pre < n_pre)) (PreH9 : (n_pre <= INT_MAX)) (PreH10 : ((Znth (root_pre) (vis2_l_low_level_spec) (0)) <> 0)) ,
  TT && emp 
|--
  “ (0 <= (Znth u_pre fadj_row_l_low_level_spec 0)) ”
.

Definition dfs2_entail_wit_1_split_goal_7 := 
forall (n_pre: Z) (u_pre: Z) (root_pre: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (root_v_low_level_spec: Z) (sid_l_low_level_spec: (@list Z)) (vis2_l_low_level_spec: (@list Z)) (fadj_row_l_low_level_spec: (@list Z)) (fadj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (PreH1 : (csr_wf2 g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec vis2_l_low_level_spec sid_l_low_level_spec )) (PreH2 : (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH3 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH4 : (safeExec (pre_dfs2 (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (vis2_l_low_level_spec) (sid_l_low_level_spec) (root_v_low_level_spec)) (dfs_scc (g_low_level_spec) (root_pre) (u_pre)) X_low_level_spec )) (PreH5 : (0 <= u_pre)) (PreH6 : (u_pre < n_pre)) (PreH7 : (0 <= root_pre)) (PreH8 : (root_pre < n_pre)) (PreH9 : (n_pre <= INT_MAX)) (PreH10 : ((Znth (root_pre) (vis2_l_low_level_spec) (0)) <> 0)) ,
  TT && emp 
|--
  “ ((Znth (u_pre + 1 ) fadj_row_l_low_level_spec 0) = (csr_hi (u_pre) (fadj_row_l_low_level_spec))) ”
.

Definition dfs2_entail_wit_1_split_goal_8 := 
forall (n_pre: Z) (u_pre: Z) (root_pre: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (root_v_low_level_spec: Z) (sid_l_low_level_spec: (@list Z)) (vis2_l_low_level_spec: (@list Z)) (fadj_row_l_low_level_spec: (@list Z)) (fadj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (PreH1 : (csr_wf2 g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec vis2_l_low_level_spec sid_l_low_level_spec )) (PreH2 : (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH3 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH4 : (safeExec (pre_dfs2 (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (vis2_l_low_level_spec) (sid_l_low_level_spec) (root_v_low_level_spec)) (dfs_scc (g_low_level_spec) (root_pre) (u_pre)) X_low_level_spec )) (PreH5 : (0 <= u_pre)) (PreH6 : (u_pre < n_pre)) (PreH7 : (0 <= root_pre)) (PreH8 : (root_pre < n_pre)) (PreH9 : (n_pre <= INT_MAX)) (PreH10 : ((Znth (root_pre) (vis2_l_low_level_spec) (0)) <> 0)) ,
  TT && emp 
|--
  “ ((Znth u_pre fadj_row_l_low_level_spec 0) = (csr_lo (u_pre) (fadj_row_l_low_level_spec))) ”
.

Definition dfs2_entail_wit_1_split_goal_9 := 
forall (n_pre: Z) (u_pre: Z) (root_pre: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (root_v_low_level_spec: Z) (sid_l_low_level_spec: (@list Z)) (vis2_l_low_level_spec: (@list Z)) (fadj_row_l_low_level_spec: (@list Z)) (fadj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (PreH1 : (csr_wf2 g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec vis2_l_low_level_spec sid_l_low_level_spec )) (PreH2 : (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH3 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH4 : (safeExec (pre_dfs2 (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (vis2_l_low_level_spec) (sid_l_low_level_spec) (root_v_low_level_spec)) (dfs_scc (g_low_level_spec) (root_pre) (u_pre)) X_low_level_spec )) (PreH5 : (0 <= u_pre)) (PreH6 : (u_pre < n_pre)) (PreH7 : (0 <= root_pre)) (PreH8 : (root_pre < n_pre)) (PreH9 : (n_pre <= INT_MAX)) (PreH10 : ((Znth (root_pre) (vis2_l_low_level_spec) (0)) <> 0)) ,
  TT && emp 
|--
  “ (safeExec (pre_dfs2 (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) ((replace_Znth (u_pre) (1) (vis2_l_low_level_spec))) ((replace_Znth (u_pre) ((Znth root_pre sid_l_low_level_spec 0)) (sid_l_low_level_spec))) (root_v_low_level_spec)) (dfs_scc_from (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (root_pre) (u_pre) ((Znth u_pre fadj_row_l_low_level_spec 0))) X_low_level_spec ) ”
.

Definition dfs2_entail_wit_1_split_goal_10 := 
forall (n_pre: Z) (u_pre: Z) (root_pre: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (root_v_low_level_spec: Z) (sid_l_low_level_spec: (@list Z)) (vis2_l_low_level_spec: (@list Z)) (fadj_row_l_low_level_spec: (@list Z)) (fadj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (PreH1 : (csr_wf2 g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec vis2_l_low_level_spec sid_l_low_level_spec )) (PreH2 : (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH3 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH4 : (safeExec (pre_dfs2 (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (vis2_l_low_level_spec) (sid_l_low_level_spec) (root_v_low_level_spec)) (dfs_scc (g_low_level_spec) (root_pre) (u_pre)) X_low_level_spec )) (PreH5 : (0 <= u_pre)) (PreH6 : (u_pre < n_pre)) (PreH7 : (0 <= root_pre)) (PreH8 : (root_pre < n_pre)) (PreH9 : (n_pre <= INT_MAX)) (PreH10 : ((Znth (root_pre) (vis2_l_low_level_spec) (0)) <> 0)) ,
  TT && emp 
|--
  “ (csr_wf2 g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec (replace_Znth (u_pre) (1) (vis2_l_low_level_spec)) (replace_Znth (u_pre) ((Znth root_pre sid_l_low_level_spec 0)) (sid_l_low_level_spec)) ) ”
.

Definition dfs2_entail_wit_2 := 
(
forall (sid_pre: Z) (vis2_pre: Z) (fadj_row_pre: Z) (fadj_col_pre: Z) (n_pre: Z) (u_pre: Z) (root_pre: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (root_v_low_level_spec: Z) (vis2_l_low_level_spec: (@list Z)) (fadj_row_l_low_level_spec: (@list Z)) (fadj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (hi: Z) (lo: Z) (i: Z) (vis2_m: (@list Z)) (sid_m: (@list Z)) (PreH1 : (i < hi)) (PreH2 : (csr_wf2 g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec vis2_m sid_m )) (PreH3 : (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH4 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH5 : (safeExec (pre_dfs2 (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (vis2_m) (sid_m) (root_v_low_level_spec)) (dfs_scc_from (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (root_pre) (u_pre) (i)) X_low_level_spec )) (PreH6 : (lo = (csr_lo (u_pre) (fadj_row_l_low_level_spec)))) (PreH7 : (hi = (csr_hi (u_pre) (fadj_row_l_low_level_spec)))) (PreH8 : (0 <= lo)) (PreH9 : (lo <= i)) (PreH10 : (i <= hi)) (PreH11 : (hi <= (m_of (fadj_row_l_low_level_spec)))) (PreH12 : (0 <= u_pre)) (PreH13 : (u_pre < n_pre)) (PreH14 : (0 <= root_pre)) (PreH15 : (root_pre < n_pre)) (PreH16 : (n_pre <= INT_MAX)) (PreH17 : ((Znth (u_pre) (vis2_m) (0)) <> 0)) (PreH18 : forall (j_2: Z) , (((lo <= j_2) /\ (j_2 < i)) -> ((Znth ((Znth (j_2) (fadj_col_l_low_level_spec) (0))) (vis2_m) (0)) <> 0))) (PreH19 : ((Znth (root_pre) (vis2_m) (0)) <> 0)) (PreH20 : forall (w_2: Z) , (((0 <= w_2) /\ (w_2 < n_pre)) -> (((Znth (w_2) (vis2_l_low_level_spec) (0)) <> 0) -> ((Znth (w_2) (vis2_m) (0)) <> 0)))) ,
  (IntArray.full fadj_col_pre (m_of (fadj_row_l_low_level_spec)) fadj_col_l_low_level_spec )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_low_level_spec )
  **  (IntArray.full vis2_pre n_pre vis2_m )
  **  (IntArray.full sid_pre n_pre sid_m )
|--
  “ (csr_wf2 g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec vis2_m sid_m ) ” 
  &&  “ (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec ) ” 
  &&  “ ((adj_verts (g_low_level_spec)) = n_pre) ” 
  &&  “ (safeExec (pre_dfs2 (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (vis2_m) (sid_m) (root_v_low_level_spec)) (dfs_scc_from (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (root_pre) (u_pre) (i)) X_low_level_spec ) ” 
  &&  “ (lo = (csr_lo (u_pre) (fadj_row_l_low_level_spec))) ” 
  &&  “ (hi = (csr_hi (u_pre) (fadj_row_l_low_level_spec))) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= i) ” 
  &&  “ (i < hi) ” 
  &&  “ (hi <= (m_of (fadj_row_l_low_level_spec))) ” 
  &&  “ (0 <= u_pre) ” 
  &&  “ (u_pre < n_pre) ” 
  &&  “ (0 <= root_pre) ” 
  &&  “ (root_pre < n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ ((Znth (u_pre) (vis2_m) (0)) <> 0) ” 
  &&  “ forall (j: Z) , (((lo <= j) /\ (j < i)) -> ((Znth ((Znth (j) (fadj_col_l_low_level_spec) (0))) (vis2_m) (0)) <> 0)) ” 
  &&  “ ((Znth (root_pre) (vis2_m) (0)) <> 0) ” 
  &&  “ forall (w: Z) , (((0 <= w) /\ (w < n_pre)) -> (((Znth (w) (vis2_l_low_level_spec) (0)) <> 0) -> ((Znth (w) (vis2_m) (0)) <> 0))) ” 
  &&  “ (0 <= (Znth i fadj_col_l_low_level_spec 0)) ” 
  &&  “ ((Znth i fadj_col_l_low_level_spec 0) < n_pre) ” 
  &&  “ ((Znth i fadj_col_l_low_level_spec 0) = (Znth (i) (fadj_col_l_low_level_spec) (0))) ”
  &&  (IntArray.full fadj_col_pre (m_of (fadj_row_l_low_level_spec)) fadj_col_l_low_level_spec )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_low_level_spec )
  **  (IntArray.full vis2_pre n_pre vis2_m )
  **  (IntArray.full sid_pre n_pre sid_m )
) \/
(
forall (n_pre: Z) (u_pre: Z) (root_pre: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (root_v_low_level_spec: Z) (vis2_l_low_level_spec: (@list Z)) (fadj_row_l_low_level_spec: (@list Z)) (fadj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (hi: Z) (lo: Z) (i: Z) (vis2_m: (@list Z)) (sid_m: (@list Z)) (PreH1 : (i < hi)) (PreH2 : (csr_wf2 g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec vis2_m sid_m )) (PreH3 : (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH4 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH5 : (safeExec (pre_dfs2 (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (vis2_m) (sid_m) (root_v_low_level_spec)) (dfs_scc_from (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (root_pre) (u_pre) (i)) X_low_level_spec )) (PreH6 : (lo = (csr_lo (u_pre) (fadj_row_l_low_level_spec)))) (PreH7 : (hi = (csr_hi (u_pre) (fadj_row_l_low_level_spec)))) (PreH8 : (0 <= lo)) (PreH9 : (lo <= i)) (PreH10 : (i <= hi)) (PreH11 : (hi <= (m_of (fadj_row_l_low_level_spec)))) (PreH12 : (0 <= u_pre)) (PreH13 : (u_pre < n_pre)) (PreH14 : (0 <= root_pre)) (PreH15 : (root_pre < n_pre)) (PreH16 : (n_pre <= INT_MAX)) (PreH17 : ((Znth (u_pre) (vis2_m) (0)) <> 0)) (PreH18 : forall (j_2: Z) , (((lo <= j_2) /\ (j_2 < i)) -> ((Znth ((Znth (j_2) (fadj_col_l_low_level_spec) (0))) (vis2_m) (0)) <> 0))) (PreH19 : ((Znth (root_pre) (vis2_m) (0)) <> 0)) (PreH20 : forall (w_2: Z) , (((0 <= w_2) /\ (w_2 < n_pre)) -> (((Znth (w_2) (vis2_l_low_level_spec) (0)) <> 0) -> ((Znth (w_2) (vis2_m) (0)) <> 0)))) ,
  TT && emp 
|--
  “ ((Znth i fadj_col_l_low_level_spec 0) = (Znth (i) (fadj_col_l_low_level_spec) (0))) ” 
  &&  “ ((Znth i fadj_col_l_low_level_spec 0) < n_pre) ” 
  &&  “ (0 <= (Znth i fadj_col_l_low_level_spec 0)) ”
  &&  emp
).

Definition dfs2_entail_wit_2_split_goal_1 := 
forall (n_pre: Z) (u_pre: Z) (root_pre: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (root_v_low_level_spec: Z) (vis2_l_low_level_spec: (@list Z)) (fadj_row_l_low_level_spec: (@list Z)) (fadj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (hi: Z) (lo: Z) (i: Z) (vis2_m: (@list Z)) (sid_m: (@list Z)) (PreH1 : (i < hi)) (PreH2 : (csr_wf2 g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec vis2_m sid_m )) (PreH3 : (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH4 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH5 : (safeExec (pre_dfs2 (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (vis2_m) (sid_m) (root_v_low_level_spec)) (dfs_scc_from (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (root_pre) (u_pre) (i)) X_low_level_spec )) (PreH6 : (lo = (csr_lo (u_pre) (fadj_row_l_low_level_spec)))) (PreH7 : (hi = (csr_hi (u_pre) (fadj_row_l_low_level_spec)))) (PreH8 : (0 <= lo)) (PreH9 : (lo <= i)) (PreH10 : (i <= hi)) (PreH11 : (hi <= (m_of (fadj_row_l_low_level_spec)))) (PreH12 : (0 <= u_pre)) (PreH13 : (u_pre < n_pre)) (PreH14 : (0 <= root_pre)) (PreH15 : (root_pre < n_pre)) (PreH16 : (n_pre <= INT_MAX)) (PreH17 : ((Znth (u_pre) (vis2_m) (0)) <> 0)) (PreH18 : forall (j_2: Z) , (((lo <= j_2) /\ (j_2 < i)) -> ((Znth ((Znth (j_2) (fadj_col_l_low_level_spec) (0))) (vis2_m) (0)) <> 0))) (PreH19 : ((Znth (root_pre) (vis2_m) (0)) <> 0)) (PreH20 : forall (w_2: Z) , (((0 <= w_2) /\ (w_2 < n_pre)) -> (((Znth (w_2) (vis2_l_low_level_spec) (0)) <> 0) -> ((Znth (w_2) (vis2_m) (0)) <> 0)))) ,
  TT && emp 
|--
  “ ((Znth i fadj_col_l_low_level_spec 0) = (Znth (i) (fadj_col_l_low_level_spec) (0))) ”
.

Definition dfs2_entail_wit_2_split_goal_2 := 
forall (n_pre: Z) (u_pre: Z) (root_pre: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (root_v_low_level_spec: Z) (vis2_l_low_level_spec: (@list Z)) (fadj_row_l_low_level_spec: (@list Z)) (fadj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (hi: Z) (lo: Z) (i: Z) (vis2_m: (@list Z)) (sid_m: (@list Z)) (PreH1 : (i < hi)) (PreH2 : (csr_wf2 g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec vis2_m sid_m )) (PreH3 : (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH4 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH5 : (safeExec (pre_dfs2 (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (vis2_m) (sid_m) (root_v_low_level_spec)) (dfs_scc_from (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (root_pre) (u_pre) (i)) X_low_level_spec )) (PreH6 : (lo = (csr_lo (u_pre) (fadj_row_l_low_level_spec)))) (PreH7 : (hi = (csr_hi (u_pre) (fadj_row_l_low_level_spec)))) (PreH8 : (0 <= lo)) (PreH9 : (lo <= i)) (PreH10 : (i <= hi)) (PreH11 : (hi <= (m_of (fadj_row_l_low_level_spec)))) (PreH12 : (0 <= u_pre)) (PreH13 : (u_pre < n_pre)) (PreH14 : (0 <= root_pre)) (PreH15 : (root_pre < n_pre)) (PreH16 : (n_pre <= INT_MAX)) (PreH17 : ((Znth (u_pre) (vis2_m) (0)) <> 0)) (PreH18 : forall (j_2: Z) , (((lo <= j_2) /\ (j_2 < i)) -> ((Znth ((Znth (j_2) (fadj_col_l_low_level_spec) (0))) (vis2_m) (0)) <> 0))) (PreH19 : ((Znth (root_pre) (vis2_m) (0)) <> 0)) (PreH20 : forall (w_2: Z) , (((0 <= w_2) /\ (w_2 < n_pre)) -> (((Znth (w_2) (vis2_l_low_level_spec) (0)) <> 0) -> ((Znth (w_2) (vis2_m) (0)) <> 0)))) ,
  TT && emp 
|--
  “ ((Znth i fadj_col_l_low_level_spec 0) < n_pre) ”
.

Definition dfs2_entail_wit_2_split_goal_3 := 
forall (n_pre: Z) (u_pre: Z) (root_pre: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (root_v_low_level_spec: Z) (vis2_l_low_level_spec: (@list Z)) (fadj_row_l_low_level_spec: (@list Z)) (fadj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (hi: Z) (lo: Z) (i: Z) (vis2_m: (@list Z)) (sid_m: (@list Z)) (PreH1 : (i < hi)) (PreH2 : (csr_wf2 g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec vis2_m sid_m )) (PreH3 : (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH4 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH5 : (safeExec (pre_dfs2 (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (vis2_m) (sid_m) (root_v_low_level_spec)) (dfs_scc_from (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (root_pre) (u_pre) (i)) X_low_level_spec )) (PreH6 : (lo = (csr_lo (u_pre) (fadj_row_l_low_level_spec)))) (PreH7 : (hi = (csr_hi (u_pre) (fadj_row_l_low_level_spec)))) (PreH8 : (0 <= lo)) (PreH9 : (lo <= i)) (PreH10 : (i <= hi)) (PreH11 : (hi <= (m_of (fadj_row_l_low_level_spec)))) (PreH12 : (0 <= u_pre)) (PreH13 : (u_pre < n_pre)) (PreH14 : (0 <= root_pre)) (PreH15 : (root_pre < n_pre)) (PreH16 : (n_pre <= INT_MAX)) (PreH17 : ((Znth (u_pre) (vis2_m) (0)) <> 0)) (PreH18 : forall (j_2: Z) , (((lo <= j_2) /\ (j_2 < i)) -> ((Znth ((Znth (j_2) (fadj_col_l_low_level_spec) (0))) (vis2_m) (0)) <> 0))) (PreH19 : ((Znth (root_pre) (vis2_m) (0)) <> 0)) (PreH20 : forall (w_2: Z) , (((0 <= w_2) /\ (w_2 < n_pre)) -> (((Znth (w_2) (vis2_l_low_level_spec) (0)) <> 0) -> ((Znth (w_2) (vis2_m) (0)) <> 0)))) ,
  TT && emp 
|--
  “ (0 <= (Znth i fadj_col_l_low_level_spec 0)) ”
.

Definition dfs2_entail_wit_3_1 := 
(
forall (sid_pre: Z) (vis2_pre: Z) (fadj_row_pre: Z) (fadj_col_pre: Z) (n_pre: Z) (u_pre: Z) (root_pre: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (root_v_low_level_spec: Z) (vis2_l_low_level_spec: (@list Z)) (fadj_row_l_low_level_spec: (@list Z)) (fadj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (vis2_m_2: (@list Z)) (sid_m_2: (@list Z)) (i: Z) (lo: Z) (hi: Z) (v: Z) (vis2_l_: (@list Z)) (sid_l_: (@list Z)) (PreH1 : (csr_wf2 g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec vis2_l_ sid_l_ )) (PreH2 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH3 : (safeExec (pre_dfs2 (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (vis2_l_) (sid_l_) (root_v_low_level_spec)) (applyf ((dfs_scc_fromK (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (root_pre) (u_pre) ((i + 1 )))) (tt)) X_low_level_spec )) (PreH4 : ((Znth (v) (vis2_l_) (0)) <> 0)) (PreH5 : forall (w_2: Z) , (((0 <= w_2) /\ (w_2 < n_pre)) -> (((Znth (w_2) (vis2_m_2) (0)) <> 0) -> ((Znth (w_2) (vis2_l_) (0)) <> 0)))) (PreH6 : ((Znth v vis2_m_2 0) = 0)) (PreH7 : (csr_wf2 g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec vis2_m_2 sid_m_2 )) (PreH8 : (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH9 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH10 : (lo = (csr_lo (u_pre) (fadj_row_l_low_level_spec)))) (PreH11 : (hi = (csr_hi (u_pre) (fadj_row_l_low_level_spec)))) (PreH12 : (0 <= lo)) (PreH13 : (lo <= i)) (PreH14 : (i < hi)) (PreH15 : (hi <= (m_of (fadj_row_l_low_level_spec)))) (PreH16 : (0 <= u_pre)) (PreH17 : (u_pre < n_pre)) (PreH18 : (0 <= root_pre)) (PreH19 : (root_pre < n_pre)) (PreH20 : (n_pre <= INT_MAX)) (PreH21 : ((Znth (u_pre) (vis2_m_2) (0)) <> 0)) (PreH22 : forall (j_2: Z) , (((lo <= j_2) /\ (j_2 < i)) -> ((Znth ((Znth (j_2) (fadj_col_l_low_level_spec) (0))) (vis2_m_2) (0)) <> 0))) (PreH23 : ((Znth (root_pre) (vis2_m_2) (0)) <> 0)) (PreH24 : forall (w_3: Z) , (((0 <= w_3) /\ (w_3 < n_pre)) -> (((Znth (w_3) (vis2_l_low_level_spec) (0)) <> 0) -> ((Znth (w_3) (vis2_m_2) (0)) <> 0)))) (PreH25 : (0 <= v)) (PreH26 : (v < n_pre)) (PreH27 : (v = (Znth (i) (fadj_col_l_low_level_spec) (0)))) ,
  (IntArray.full fadj_col_pre (m_of (fadj_row_l_low_level_spec)) fadj_col_l_low_level_spec )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_low_level_spec )
  **  (IntArray.full vis2_pre n_pre vis2_l_ )
  **  (IntArray.full sid_pre n_pre sid_l_ )
|--
  EX (vis2_m: (@list Z))  (sid_m: (@list Z)) ,
  “ (csr_wf2 g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec vis2_m sid_m ) ” 
  &&  “ (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec ) ” 
  &&  “ ((adj_verts (g_low_level_spec)) = n_pre) ” 
  &&  “ (safeExec (pre_dfs2 (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (vis2_m) (sid_m) (root_v_low_level_spec)) (dfs_scc_from (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (root_pre) (u_pre) ((i + 1 ))) X_low_level_spec ) ” 
  &&  “ (lo = (csr_lo (u_pre) (fadj_row_l_low_level_spec))) ” 
  &&  “ (hi = (csr_hi (u_pre) (fadj_row_l_low_level_spec))) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= hi) ” 
  &&  “ (hi <= (m_of (fadj_row_l_low_level_spec))) ” 
  &&  “ (0 <= u_pre) ” 
  &&  “ (u_pre < n_pre) ” 
  &&  “ (0 <= root_pre) ” 
  &&  “ (root_pre < n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ ((Znth (u_pre) (vis2_m) (0)) <> 0) ” 
  &&  “ forall (j: Z) , (((lo <= j) /\ (j < (i + 1 ))) -> ((Znth ((Znth (j) (fadj_col_l_low_level_spec) (0))) (vis2_m) (0)) <> 0)) ” 
  &&  “ ((Znth (root_pre) (vis2_m) (0)) <> 0) ” 
  &&  “ forall (w: Z) , (((0 <= w) /\ (w < n_pre)) -> (((Znth (w) (vis2_l_low_level_spec) (0)) <> 0) -> ((Znth (w) (vis2_m) (0)) <> 0))) ”
  &&  (IntArray.full fadj_col_pre (m_of (fadj_row_l_low_level_spec)) fadj_col_l_low_level_spec )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_low_level_spec )
  **  (IntArray.full vis2_pre n_pre vis2_m )
  **  (IntArray.full sid_pre n_pre sid_m )
) \/
(
forall (n_pre: Z) (u_pre: Z) (root_pre: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (root_v_low_level_spec: Z) (vis2_l_low_level_spec: (@list Z)) (fadj_row_l_low_level_spec: (@list Z)) (fadj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (vis2_m_2: (@list Z)) (sid_m_2: (@list Z)) (i: Z) (lo: Z) (hi: Z) (v: Z) (vis2_l_: (@list Z)) (sid_l_: (@list Z)) (PreH1 : (csr_wf2 g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec vis2_l_ sid_l_ )) (PreH2 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH3 : (safeExec (pre_dfs2 (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (vis2_l_) (sid_l_) (root_v_low_level_spec)) (applyf ((dfs_scc_fromK (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (root_pre) (u_pre) ((i + 1 )))) (tt)) X_low_level_spec )) (PreH4 : ((Znth (v) (vis2_l_) (0)) <> 0)) (PreH5 : forall (w_2: Z) , (((0 <= w_2) /\ (w_2 < n_pre)) -> (((Znth (w_2) (vis2_m_2) (0)) <> 0) -> ((Znth (w_2) (vis2_l_) (0)) <> 0)))) (PreH6 : ((Znth v vis2_m_2 0) = 0)) (PreH7 : (csr_wf2 g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec vis2_m_2 sid_m_2 )) (PreH8 : (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH9 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH10 : (lo = (csr_lo (u_pre) (fadj_row_l_low_level_spec)))) (PreH11 : (hi = (csr_hi (u_pre) (fadj_row_l_low_level_spec)))) (PreH12 : (0 <= lo)) (PreH13 : (lo <= i)) (PreH14 : (i < hi)) (PreH15 : (hi <= (m_of (fadj_row_l_low_level_spec)))) (PreH16 : (0 <= u_pre)) (PreH17 : (u_pre < n_pre)) (PreH18 : (0 <= root_pre)) (PreH19 : (root_pre < n_pre)) (PreH20 : (n_pre <= INT_MAX)) (PreH21 : ((Znth (u_pre) (vis2_m_2) (0)) <> 0)) (PreH22 : forall (j_2: Z) , (((lo <= j_2) /\ (j_2 < i)) -> ((Znth ((Znth (j_2) (fadj_col_l_low_level_spec) (0))) (vis2_m_2) (0)) <> 0))) (PreH23 : ((Znth (root_pre) (vis2_m_2) (0)) <> 0)) (PreH24 : forall (w_3: Z) , (((0 <= w_3) /\ (w_3 < n_pre)) -> (((Znth (w_3) (vis2_l_low_level_spec) (0)) <> 0) -> ((Znth (w_3) (vis2_m_2) (0)) <> 0)))) (PreH25 : (0 <= v)) (PreH26 : (v < n_pre)) (PreH27 : (v = (Znth (i) (fadj_col_l_low_level_spec) (0)))) ,
  TT && emp 
|--
  “ (((Znth ((Znth (lo) (fadj_col_l_low_level_spec) (0))) (vis2_l_) (0)) <> 0) /\ ((Znth ((Znth (((i + 1 ) - 1 )) (fadj_col_l_low_level_spec) (0))) (vis2_l_) (0)) <> 0)) ” 
  &&  “ ((Znth (u_pre) (vis2_l_) (0)) <> 0) ” 
  &&  “ (safeExec (pre_dfs2 (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (vis2_l_) (sid_l_) (root_v_low_level_spec)) (dfs_scc_from (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (root_pre) (u_pre) ((i + 1 ))) X_low_level_spec ) ”
  &&  emp
).

Definition dfs2_entail_wit_3_1_split_goal_1 := 
forall (n_pre: Z) (u_pre: Z) (root_pre: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (root_v_low_level_spec: Z) (vis2_l_low_level_spec: (@list Z)) (fadj_row_l_low_level_spec: (@list Z)) (fadj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (vis2_m_2: (@list Z)) (sid_m_2: (@list Z)) (i: Z) (lo: Z) (hi: Z) (v: Z) (vis2_l_: (@list Z)) (sid_l_: (@list Z)) (PreH1 : (csr_wf2 g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec vis2_l_ sid_l_ )) (PreH2 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH3 : (safeExec (pre_dfs2 (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (vis2_l_) (sid_l_) (root_v_low_level_spec)) (applyf ((dfs_scc_fromK (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (root_pre) (u_pre) ((i + 1 )))) (tt)) X_low_level_spec )) (PreH4 : ((Znth (v) (vis2_l_) (0)) <> 0)) (PreH5 : forall (w_2: Z) , (((0 <= w_2) /\ (w_2 < n_pre)) -> (((Znth (w_2) (vis2_m_2) (0)) <> 0) -> ((Znth (w_2) (vis2_l_) (0)) <> 0)))) (PreH6 : ((Znth v vis2_m_2 0) = 0)) (PreH7 : (csr_wf2 g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec vis2_m_2 sid_m_2 )) (PreH8 : (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH9 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH10 : (lo = (csr_lo (u_pre) (fadj_row_l_low_level_spec)))) (PreH11 : (hi = (csr_hi (u_pre) (fadj_row_l_low_level_spec)))) (PreH12 : (0 <= lo)) (PreH13 : (lo <= i)) (PreH14 : (i < hi)) (PreH15 : (hi <= (m_of (fadj_row_l_low_level_spec)))) (PreH16 : (0 <= u_pre)) (PreH17 : (u_pre < n_pre)) (PreH18 : (0 <= root_pre)) (PreH19 : (root_pre < n_pre)) (PreH20 : (n_pre <= INT_MAX)) (PreH21 : ((Znth (u_pre) (vis2_m_2) (0)) <> 0)) (PreH22 : forall (j_2: Z) , (((lo <= j_2) /\ (j_2 < i)) -> ((Znth ((Znth (j_2) (fadj_col_l_low_level_spec) (0))) (vis2_m_2) (0)) <> 0))) (PreH23 : ((Znth (root_pre) (vis2_m_2) (0)) <> 0)) (PreH24 : forall (w_3: Z) , (((0 <= w_3) /\ (w_3 < n_pre)) -> (((Znth (w_3) (vis2_l_low_level_spec) (0)) <> 0) -> ((Znth (w_3) (vis2_m_2) (0)) <> 0)))) (PreH25 : (0 <= v)) (PreH26 : (v < n_pre)) (PreH27 : (v = (Znth (i) (fadj_col_l_low_level_spec) (0)))) ,
  TT && emp 
|--
  “ (((Znth ((Znth (lo) (fadj_col_l_low_level_spec) (0))) (vis2_l_) (0)) <> 0) /\ ((Znth ((Znth (((i + 1 ) - 1 )) (fadj_col_l_low_level_spec) (0))) (vis2_l_) (0)) <> 0)) ”
.

Definition dfs2_entail_wit_3_1_split_goal_2 := 
forall (n_pre: Z) (u_pre: Z) (root_pre: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (root_v_low_level_spec: Z) (vis2_l_low_level_spec: (@list Z)) (fadj_row_l_low_level_spec: (@list Z)) (fadj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (vis2_m_2: (@list Z)) (sid_m_2: (@list Z)) (i: Z) (lo: Z) (hi: Z) (v: Z) (vis2_l_: (@list Z)) (sid_l_: (@list Z)) (PreH1 : (csr_wf2 g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec vis2_l_ sid_l_ )) (PreH2 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH3 : (safeExec (pre_dfs2 (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (vis2_l_) (sid_l_) (root_v_low_level_spec)) (applyf ((dfs_scc_fromK (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (root_pre) (u_pre) ((i + 1 )))) (tt)) X_low_level_spec )) (PreH4 : ((Znth (v) (vis2_l_) (0)) <> 0)) (PreH5 : forall (w_2: Z) , (((0 <= w_2) /\ (w_2 < n_pre)) -> (((Znth (w_2) (vis2_m_2) (0)) <> 0) -> ((Znth (w_2) (vis2_l_) (0)) <> 0)))) (PreH6 : ((Znth v vis2_m_2 0) = 0)) (PreH7 : (csr_wf2 g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec vis2_m_2 sid_m_2 )) (PreH8 : (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH9 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH10 : (lo = (csr_lo (u_pre) (fadj_row_l_low_level_spec)))) (PreH11 : (hi = (csr_hi (u_pre) (fadj_row_l_low_level_spec)))) (PreH12 : (0 <= lo)) (PreH13 : (lo <= i)) (PreH14 : (i < hi)) (PreH15 : (hi <= (m_of (fadj_row_l_low_level_spec)))) (PreH16 : (0 <= u_pre)) (PreH17 : (u_pre < n_pre)) (PreH18 : (0 <= root_pre)) (PreH19 : (root_pre < n_pre)) (PreH20 : (n_pre <= INT_MAX)) (PreH21 : ((Znth (u_pre) (vis2_m_2) (0)) <> 0)) (PreH22 : forall (j_2: Z) , (((lo <= j_2) /\ (j_2 < i)) -> ((Znth ((Znth (j_2) (fadj_col_l_low_level_spec) (0))) (vis2_m_2) (0)) <> 0))) (PreH23 : ((Znth (root_pre) (vis2_m_2) (0)) <> 0)) (PreH24 : forall (w_3: Z) , (((0 <= w_3) /\ (w_3 < n_pre)) -> (((Znth (w_3) (vis2_l_low_level_spec) (0)) <> 0) -> ((Znth (w_3) (vis2_m_2) (0)) <> 0)))) (PreH25 : (0 <= v)) (PreH26 : (v < n_pre)) (PreH27 : (v = (Znth (i) (fadj_col_l_low_level_spec) (0)))) ,
  TT && emp 
|--
  “ ((Znth (u_pre) (vis2_l_) (0)) <> 0) ”
.

Definition dfs2_entail_wit_3_1_split_goal_3 := 
forall (n_pre: Z) (u_pre: Z) (root_pre: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (root_v_low_level_spec: Z) (vis2_l_low_level_spec: (@list Z)) (fadj_row_l_low_level_spec: (@list Z)) (fadj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (vis2_m_2: (@list Z)) (sid_m_2: (@list Z)) (i: Z) (lo: Z) (hi: Z) (v: Z) (vis2_l_: (@list Z)) (sid_l_: (@list Z)) (PreH1 : (csr_wf2 g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec vis2_l_ sid_l_ )) (PreH2 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH3 : (safeExec (pre_dfs2 (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (vis2_l_) (sid_l_) (root_v_low_level_spec)) (applyf ((dfs_scc_fromK (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (root_pre) (u_pre) ((i + 1 )))) (tt)) X_low_level_spec )) (PreH4 : ((Znth (v) (vis2_l_) (0)) <> 0)) (PreH5 : forall (w_2: Z) , (((0 <= w_2) /\ (w_2 < n_pre)) -> (((Znth (w_2) (vis2_m_2) (0)) <> 0) -> ((Znth (w_2) (vis2_l_) (0)) <> 0)))) (PreH6 : ((Znth v vis2_m_2 0) = 0)) (PreH7 : (csr_wf2 g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec vis2_m_2 sid_m_2 )) (PreH8 : (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH9 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH10 : (lo = (csr_lo (u_pre) (fadj_row_l_low_level_spec)))) (PreH11 : (hi = (csr_hi (u_pre) (fadj_row_l_low_level_spec)))) (PreH12 : (0 <= lo)) (PreH13 : (lo <= i)) (PreH14 : (i < hi)) (PreH15 : (hi <= (m_of (fadj_row_l_low_level_spec)))) (PreH16 : (0 <= u_pre)) (PreH17 : (u_pre < n_pre)) (PreH18 : (0 <= root_pre)) (PreH19 : (root_pre < n_pre)) (PreH20 : (n_pre <= INT_MAX)) (PreH21 : ((Znth (u_pre) (vis2_m_2) (0)) <> 0)) (PreH22 : forall (j_2: Z) , (((lo <= j_2) /\ (j_2 < i)) -> ((Znth ((Znth (j_2) (fadj_col_l_low_level_spec) (0))) (vis2_m_2) (0)) <> 0))) (PreH23 : ((Znth (root_pre) (vis2_m_2) (0)) <> 0)) (PreH24 : forall (w_3: Z) , (((0 <= w_3) /\ (w_3 < n_pre)) -> (((Znth (w_3) (vis2_l_low_level_spec) (0)) <> 0) -> ((Znth (w_3) (vis2_m_2) (0)) <> 0)))) (PreH25 : (0 <= v)) (PreH26 : (v < n_pre)) (PreH27 : (v = (Znth (i) (fadj_col_l_low_level_spec) (0)))) ,
  TT && emp 
|--
  “ (safeExec (pre_dfs2 (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (vis2_l_) (sid_l_) (root_v_low_level_spec)) (dfs_scc_from (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (root_pre) (u_pre) ((i + 1 ))) X_low_level_spec ) ”
.

Definition dfs2_entail_wit_3_2 := 
(
forall (sid_pre: Z) (vis2_pre: Z) (fadj_row_pre: Z) (fadj_col_pre: Z) (n_pre: Z) (u_pre: Z) (root_pre: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (root_v_low_level_spec: Z) (vis2_l_low_level_spec: (@list Z)) (fadj_row_l_low_level_spec: (@list Z)) (fadj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (vis2_m_2: (@list Z)) (sid_m_2: (@list Z)) (i: Z) (lo: Z) (hi: Z) (v: Z) (PreH1 : ((Znth v vis2_m_2 0) <> 0)) (PreH2 : (csr_wf2 g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec vis2_m_2 sid_m_2 )) (PreH3 : (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH4 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH5 : (safeExec (pre_dfs2 (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (vis2_m_2) (sid_m_2) (root_v_low_level_spec)) (dfs_scc_from (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (root_pre) (u_pre) (i)) X_low_level_spec )) (PreH6 : (lo = (csr_lo (u_pre) (fadj_row_l_low_level_spec)))) (PreH7 : (hi = (csr_hi (u_pre) (fadj_row_l_low_level_spec)))) (PreH8 : (0 <= lo)) (PreH9 : (lo <= i)) (PreH10 : (i < hi)) (PreH11 : (hi <= (m_of (fadj_row_l_low_level_spec)))) (PreH12 : (0 <= u_pre)) (PreH13 : (u_pre < n_pre)) (PreH14 : (0 <= root_pre)) (PreH15 : (root_pre < n_pre)) (PreH16 : (n_pre <= INT_MAX)) (PreH17 : ((Znth (u_pre) (vis2_m_2) (0)) <> 0)) (PreH18 : forall (j_2: Z) , (((lo <= j_2) /\ (j_2 < i)) -> ((Znth ((Znth (j_2) (fadj_col_l_low_level_spec) (0))) (vis2_m_2) (0)) <> 0))) (PreH19 : ((Znth (root_pre) (vis2_m_2) (0)) <> 0)) (PreH20 : forall (w_2: Z) , (((0 <= w_2) /\ (w_2 < n_pre)) -> (((Znth (w_2) (vis2_l_low_level_spec) (0)) <> 0) -> ((Znth (w_2) (vis2_m_2) (0)) <> 0)))) (PreH21 : (0 <= v)) (PreH22 : (v < n_pre)) (PreH23 : (v = (Znth (i) (fadj_col_l_low_level_spec) (0)))) ,
  (IntArray.full vis2_pre n_pre vis2_m_2 )
  **  (IntArray.full fadj_col_pre (m_of (fadj_row_l_low_level_spec)) fadj_col_l_low_level_spec )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_low_level_spec )
  **  (IntArray.full sid_pre n_pre sid_m_2 )
|--
  EX (vis2_m: (@list Z))  (sid_m: (@list Z)) ,
  “ (csr_wf2 g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec vis2_m sid_m ) ” 
  &&  “ (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec ) ” 
  &&  “ ((adj_verts (g_low_level_spec)) = n_pre) ” 
  &&  “ (safeExec (pre_dfs2 (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (vis2_m) (sid_m) (root_v_low_level_spec)) (dfs_scc_from (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (root_pre) (u_pre) ((i + 1 ))) X_low_level_spec ) ” 
  &&  “ (lo = (csr_lo (u_pre) (fadj_row_l_low_level_spec))) ” 
  &&  “ (hi = (csr_hi (u_pre) (fadj_row_l_low_level_spec))) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= hi) ” 
  &&  “ (hi <= (m_of (fadj_row_l_low_level_spec))) ” 
  &&  “ (0 <= u_pre) ” 
  &&  “ (u_pre < n_pre) ” 
  &&  “ (0 <= root_pre) ” 
  &&  “ (root_pre < n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ ((Znth (u_pre) (vis2_m) (0)) <> 0) ” 
  &&  “ forall (j: Z) , (((lo <= j) /\ (j < (i + 1 ))) -> ((Znth ((Znth (j) (fadj_col_l_low_level_spec) (0))) (vis2_m) (0)) <> 0)) ” 
  &&  “ ((Znth (root_pre) (vis2_m) (0)) <> 0) ” 
  &&  “ forall (w: Z) , (((0 <= w) /\ (w < n_pre)) -> (((Znth (w) (vis2_l_low_level_spec) (0)) <> 0) -> ((Znth (w) (vis2_m) (0)) <> 0))) ”
  &&  (IntArray.full fadj_col_pre (m_of (fadj_row_l_low_level_spec)) fadj_col_l_low_level_spec )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_low_level_spec )
  **  (IntArray.full vis2_pre n_pre vis2_m )
  **  (IntArray.full sid_pre n_pre sid_m )
) \/
(
forall (n_pre: Z) (u_pre: Z) (root_pre: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (root_v_low_level_spec: Z) (vis2_l_low_level_spec: (@list Z)) (fadj_row_l_low_level_spec: (@list Z)) (fadj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (vis2_m_2: (@list Z)) (sid_m_2: (@list Z)) (i: Z) (lo: Z) (hi: Z) (v: Z) (PreH1 : ((Znth v vis2_m_2 0) <> 0)) (PreH2 : (csr_wf2 g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec vis2_m_2 sid_m_2 )) (PreH3 : (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH4 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH5 : (safeExec (pre_dfs2 (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (vis2_m_2) (sid_m_2) (root_v_low_level_spec)) (dfs_scc_from (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (root_pre) (u_pre) (i)) X_low_level_spec )) (PreH6 : (lo = (csr_lo (u_pre) (fadj_row_l_low_level_spec)))) (PreH7 : (hi = (csr_hi (u_pre) (fadj_row_l_low_level_spec)))) (PreH8 : (0 <= lo)) (PreH9 : (lo <= i)) (PreH10 : (i < hi)) (PreH11 : (hi <= (m_of (fadj_row_l_low_level_spec)))) (PreH12 : (0 <= u_pre)) (PreH13 : (u_pre < n_pre)) (PreH14 : (0 <= root_pre)) (PreH15 : (root_pre < n_pre)) (PreH16 : (n_pre <= INT_MAX)) (PreH17 : ((Znth (u_pre) (vis2_m_2) (0)) <> 0)) (PreH18 : forall (j_2: Z) , (((lo <= j_2) /\ (j_2 < i)) -> ((Znth ((Znth (j_2) (fadj_col_l_low_level_spec) (0))) (vis2_m_2) (0)) <> 0))) (PreH19 : ((Znth (root_pre) (vis2_m_2) (0)) <> 0)) (PreH20 : forall (w_2: Z) , (((0 <= w_2) /\ (w_2 < n_pre)) -> (((Znth (w_2) (vis2_l_low_level_spec) (0)) <> 0) -> ((Znth (w_2) (vis2_m_2) (0)) <> 0)))) (PreH21 : (0 <= v)) (PreH22 : (v < n_pre)) (PreH23 : (v = (Znth (i) (fadj_col_l_low_level_spec) (0)))) ,
  TT && emp 
|--
  “ (((Znth ((Znth (lo) (fadj_col_l_low_level_spec) (0))) (vis2_m_2) (0)) <> 0) /\ ((Znth ((Znth (((i + 1 ) - 1 )) (fadj_col_l_low_level_spec) (0))) (vis2_m_2) (0)) <> 0)) ” 
  &&  “ (safeExec (pre_dfs2 (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (vis2_m_2) (sid_m_2) (root_v_low_level_spec)) (dfs_scc_from (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (root_pre) (u_pre) ((i + 1 ))) X_low_level_spec ) ”
  &&  emp
).

Definition dfs2_entail_wit_3_2_split_goal_1 := 
forall (n_pre: Z) (u_pre: Z) (root_pre: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (root_v_low_level_spec: Z) (vis2_l_low_level_spec: (@list Z)) (fadj_row_l_low_level_spec: (@list Z)) (fadj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (vis2_m_2: (@list Z)) (sid_m_2: (@list Z)) (i: Z) (lo: Z) (hi: Z) (v: Z) (PreH1 : ((Znth v vis2_m_2 0) <> 0)) (PreH2 : (csr_wf2 g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec vis2_m_2 sid_m_2 )) (PreH3 : (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH4 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH5 : (safeExec (pre_dfs2 (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (vis2_m_2) (sid_m_2) (root_v_low_level_spec)) (dfs_scc_from (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (root_pre) (u_pre) (i)) X_low_level_spec )) (PreH6 : (lo = (csr_lo (u_pre) (fadj_row_l_low_level_spec)))) (PreH7 : (hi = (csr_hi (u_pre) (fadj_row_l_low_level_spec)))) (PreH8 : (0 <= lo)) (PreH9 : (lo <= i)) (PreH10 : (i < hi)) (PreH11 : (hi <= (m_of (fadj_row_l_low_level_spec)))) (PreH12 : (0 <= u_pre)) (PreH13 : (u_pre < n_pre)) (PreH14 : (0 <= root_pre)) (PreH15 : (root_pre < n_pre)) (PreH16 : (n_pre <= INT_MAX)) (PreH17 : ((Znth (u_pre) (vis2_m_2) (0)) <> 0)) (PreH18 : forall (j_2: Z) , (((lo <= j_2) /\ (j_2 < i)) -> ((Znth ((Znth (j_2) (fadj_col_l_low_level_spec) (0))) (vis2_m_2) (0)) <> 0))) (PreH19 : ((Znth (root_pre) (vis2_m_2) (0)) <> 0)) (PreH20 : forall (w_2: Z) , (((0 <= w_2) /\ (w_2 < n_pre)) -> (((Znth (w_2) (vis2_l_low_level_spec) (0)) <> 0) -> ((Znth (w_2) (vis2_m_2) (0)) <> 0)))) (PreH21 : (0 <= v)) (PreH22 : (v < n_pre)) (PreH23 : (v = (Znth (i) (fadj_col_l_low_level_spec) (0)))) ,
  TT && emp 
|--
  “ (((Znth ((Znth (lo) (fadj_col_l_low_level_spec) (0))) (vis2_m_2) (0)) <> 0) /\ ((Znth ((Znth (((i + 1 ) - 1 )) (fadj_col_l_low_level_spec) (0))) (vis2_m_2) (0)) <> 0)) ”
.

Definition dfs2_entail_wit_3_2_split_goal_2 := 
forall (n_pre: Z) (u_pre: Z) (root_pre: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (root_v_low_level_spec: Z) (vis2_l_low_level_spec: (@list Z)) (fadj_row_l_low_level_spec: (@list Z)) (fadj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (vis2_m_2: (@list Z)) (sid_m_2: (@list Z)) (i: Z) (lo: Z) (hi: Z) (v: Z) (PreH1 : ((Znth v vis2_m_2 0) <> 0)) (PreH2 : (csr_wf2 g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec vis2_m_2 sid_m_2 )) (PreH3 : (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH4 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH5 : (safeExec (pre_dfs2 (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (vis2_m_2) (sid_m_2) (root_v_low_level_spec)) (dfs_scc_from (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (root_pre) (u_pre) (i)) X_low_level_spec )) (PreH6 : (lo = (csr_lo (u_pre) (fadj_row_l_low_level_spec)))) (PreH7 : (hi = (csr_hi (u_pre) (fadj_row_l_low_level_spec)))) (PreH8 : (0 <= lo)) (PreH9 : (lo <= i)) (PreH10 : (i < hi)) (PreH11 : (hi <= (m_of (fadj_row_l_low_level_spec)))) (PreH12 : (0 <= u_pre)) (PreH13 : (u_pre < n_pre)) (PreH14 : (0 <= root_pre)) (PreH15 : (root_pre < n_pre)) (PreH16 : (n_pre <= INT_MAX)) (PreH17 : ((Znth (u_pre) (vis2_m_2) (0)) <> 0)) (PreH18 : forall (j_2: Z) , (((lo <= j_2) /\ (j_2 < i)) -> ((Znth ((Znth (j_2) (fadj_col_l_low_level_spec) (0))) (vis2_m_2) (0)) <> 0))) (PreH19 : ((Znth (root_pre) (vis2_m_2) (0)) <> 0)) (PreH20 : forall (w_2: Z) , (((0 <= w_2) /\ (w_2 < n_pre)) -> (((Znth (w_2) (vis2_l_low_level_spec) (0)) <> 0) -> ((Znth (w_2) (vis2_m_2) (0)) <> 0)))) (PreH21 : (0 <= v)) (PreH22 : (v < n_pre)) (PreH23 : (v = (Znth (i) (fadj_col_l_low_level_spec) (0)))) ,
  TT && emp 
|--
  “ (safeExec (pre_dfs2 (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (vis2_m_2) (sid_m_2) (root_v_low_level_spec)) (dfs_scc_from (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (root_pre) (u_pre) ((i + 1 ))) X_low_level_spec ) ”
.

Definition dfs2_return_wit_1 := 
(
forall (sid_pre: Z) (vis2_pre: Z) (fadj_row_pre: Z) (fadj_col_pre: Z) (n_pre: Z) (u_pre: Z) (root_pre: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (root_v_low_level_spec: Z) (vis2_l_low_level_spec: (@list Z)) (fadj_row_l_low_level_spec: (@list Z)) (fadj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (hi: Z) (lo: Z) (i: Z) (vis2_m: (@list Z)) (sid_m: (@list Z)) (PreH1 : (i >= hi)) (PreH2 : (csr_wf2 g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec vis2_m sid_m )) (PreH3 : (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH4 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH5 : (safeExec (pre_dfs2 (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (vis2_m) (sid_m) (root_v_low_level_spec)) (dfs_scc_from (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (root_pre) (u_pre) (i)) X_low_level_spec )) (PreH6 : (lo = (csr_lo (u_pre) (fadj_row_l_low_level_spec)))) (PreH7 : (hi = (csr_hi (u_pre) (fadj_row_l_low_level_spec)))) (PreH8 : (0 <= lo)) (PreH9 : (lo <= i)) (PreH10 : (i <= hi)) (PreH11 : (hi <= (m_of (fadj_row_l_low_level_spec)))) (PreH12 : (0 <= u_pre)) (PreH13 : (u_pre < n_pre)) (PreH14 : (0 <= root_pre)) (PreH15 : (root_pre < n_pre)) (PreH16 : (n_pre <= INT_MAX)) (PreH17 : ((Znth (u_pre) (vis2_m) (0)) <> 0)) (PreH18 : forall (j: Z) , (((lo <= j) /\ (j < i)) -> ((Znth ((Znth (j) (fadj_col_l_low_level_spec) (0))) (vis2_m) (0)) <> 0))) (PreH19 : ((Znth (root_pre) (vis2_m) (0)) <> 0)) (PreH20 : forall (w_2: Z) , (((0 <= w_2) /\ (w_2 < n_pre)) -> (((Znth (w_2) (vis2_l_low_level_spec) (0)) <> 0) -> ((Znth (w_2) (vis2_m) (0)) <> 0)))) ,
  (IntArray.full fadj_col_pre (m_of (fadj_row_l_low_level_spec)) fadj_col_l_low_level_spec )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_low_level_spec )
  **  (IntArray.full vis2_pre n_pre vis2_m )
  **  (IntArray.full sid_pre n_pre sid_m )
|--
  EX (vis2_l_: (@list Z))  (sid_l_: (@list Z)) ,
  “ (csr_wf2 g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec vis2_l_ sid_l_ ) ” 
  &&  “ ((adj_verts (g_low_level_spec)) = n_pre) ” 
  &&  “ (safeExec (pre_dfs2 (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (vis2_l_) (sid_l_) (root_v_low_level_spec)) (return (tt)) X_low_level_spec ) ” 
  &&  “ ((Znth (u_pre) (vis2_l_) (0)) <> 0) ” 
  &&  “ forall (w: Z) , (((0 <= w) /\ (w < n_pre)) -> (((Znth (w) (vis2_l_low_level_spec) (0)) <> 0) -> ((Znth (w) (vis2_l_) (0)) <> 0))) ”
  &&  (IntArray.full fadj_col_pre (m_of (fadj_row_l_low_level_spec)) fadj_col_l_low_level_spec )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_low_level_spec )
  **  (IntArray.full vis2_pre n_pre vis2_l_ )
  **  (IntArray.full sid_pre n_pre sid_l_ )
) \/
(
forall (n_pre: Z) (u_pre: Z) (root_pre: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (root_v_low_level_spec: Z) (vis2_l_low_level_spec: (@list Z)) (fadj_row_l_low_level_spec: (@list Z)) (fadj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (hi: Z) (lo: Z) (i: Z) (vis2_m: (@list Z)) (sid_m: (@list Z)) (PreH1 : (i >= hi)) (PreH2 : (csr_wf2 g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec vis2_m sid_m )) (PreH3 : (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH4 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH5 : (safeExec (pre_dfs2 (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (vis2_m) (sid_m) (root_v_low_level_spec)) (dfs_scc_from (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (root_pre) (u_pre) (i)) X_low_level_spec )) (PreH6 : (lo = (csr_lo (u_pre) (fadj_row_l_low_level_spec)))) (PreH7 : (hi = (csr_hi (u_pre) (fadj_row_l_low_level_spec)))) (PreH8 : (0 <= lo)) (PreH9 : (lo <= i)) (PreH10 : (i <= hi)) (PreH11 : (hi <= (m_of (fadj_row_l_low_level_spec)))) (PreH12 : (0 <= u_pre)) (PreH13 : (u_pre < n_pre)) (PreH14 : (0 <= root_pre)) (PreH15 : (root_pre < n_pre)) (PreH16 : (n_pre <= INT_MAX)) (PreH17 : ((Znth (u_pre) (vis2_m) (0)) <> 0)) (PreH18 : forall (j: Z) , (((lo <= j) /\ (j < i)) -> ((Znth ((Znth (j) (fadj_col_l_low_level_spec) (0))) (vis2_m) (0)) <> 0))) (PreH19 : ((Znth (root_pre) (vis2_m) (0)) <> 0)) (PreH20 : forall (w_2: Z) , (((0 <= w_2) /\ (w_2 < n_pre)) -> (((Znth (w_2) (vis2_l_low_level_spec) (0)) <> 0) -> ((Znth (w_2) (vis2_m) (0)) <> 0)))) ,
  TT && emp 
|--
  “ (safeExec (pre_dfs2 (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (vis2_m) (sid_m) (root_v_low_level_spec)) (return (tt)) X_low_level_spec ) ”
  &&  emp
).

Definition dfs2_return_wit_1_split_goal_1 := 
forall (n_pre: Z) (u_pre: Z) (root_pre: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (root_v_low_level_spec: Z) (vis2_l_low_level_spec: (@list Z)) (fadj_row_l_low_level_spec: (@list Z)) (fadj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (hi: Z) (lo: Z) (i: Z) (vis2_m: (@list Z)) (sid_m: (@list Z)) (PreH1 : (i >= hi)) (PreH2 : (csr_wf2 g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec vis2_m sid_m )) (PreH3 : (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH4 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH5 : (safeExec (pre_dfs2 (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (vis2_m) (sid_m) (root_v_low_level_spec)) (dfs_scc_from (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (root_pre) (u_pre) (i)) X_low_level_spec )) (PreH6 : (lo = (csr_lo (u_pre) (fadj_row_l_low_level_spec)))) (PreH7 : (hi = (csr_hi (u_pre) (fadj_row_l_low_level_spec)))) (PreH8 : (0 <= lo)) (PreH9 : (lo <= i)) (PreH10 : (i <= hi)) (PreH11 : (hi <= (m_of (fadj_row_l_low_level_spec)))) (PreH12 : (0 <= u_pre)) (PreH13 : (u_pre < n_pre)) (PreH14 : (0 <= root_pre)) (PreH15 : (root_pre < n_pre)) (PreH16 : (n_pre <= INT_MAX)) (PreH17 : ((Znth (u_pre) (vis2_m) (0)) <> 0)) (PreH18 : forall (j: Z) , (((lo <= j) /\ (j < i)) -> ((Znth ((Znth (j) (fadj_col_l_low_level_spec) (0))) (vis2_m) (0)) <> 0))) (PreH19 : ((Znth (root_pre) (vis2_m) (0)) <> 0)) (PreH20 : forall (w_2: Z) , (((0 <= w_2) /\ (w_2 < n_pre)) -> (((Znth (w_2) (vis2_l_low_level_spec) (0)) <> 0) -> ((Znth (w_2) (vis2_m) (0)) <> 0)))) ,
  TT && emp 
|--
  “ (safeExec (pre_dfs2 (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (vis2_m) (sid_m) (root_v_low_level_spec)) (return (tt)) X_low_level_spec ) ”
.

Definition dfs2_partial_solve_wit_1 := 
forall (sid_pre: Z) (vis2_pre: Z) (fadj_row_pre: Z) (fadj_col_pre: Z) (n_pre: Z) (u_pre: Z) (root_pre: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (root_v_low_level_spec: Z) (sid_l_low_level_spec: (@list Z)) (vis2_l_low_level_spec: (@list Z)) (fadj_row_l_low_level_spec: (@list Z)) (fadj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (PreH1 : (csr_wf2 g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec vis2_l_low_level_spec sid_l_low_level_spec )) (PreH2 : (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH3 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH4 : (safeExec (pre_dfs2 (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (vis2_l_low_level_spec) (sid_l_low_level_spec) (root_v_low_level_spec)) (dfs_scc (g_low_level_spec) (root_pre) (u_pre)) X_low_level_spec )) (PreH5 : (0 <= u_pre)) (PreH6 : (u_pre < n_pre)) (PreH7 : (0 <= root_pre)) (PreH8 : (root_pre < n_pre)) (PreH9 : (n_pre <= INT_MAX)) (PreH10 : ((Znth (root_pre) (vis2_l_low_level_spec) (0)) <> 0)) ,
  (IntArray.full fadj_col_pre (m_of (fadj_row_l_low_level_spec)) fadj_col_l_low_level_spec )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_low_level_spec )
  **  (IntArray.full vis2_pre n_pre vis2_l_low_level_spec )
  **  (IntArray.full sid_pre n_pre sid_l_low_level_spec )
|--
  “ (csr_wf2 g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec vis2_l_low_level_spec sid_l_low_level_spec ) ” 
  &&  “ (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec ) ” 
  &&  “ ((adj_verts (g_low_level_spec)) = n_pre) ” 
  &&  “ (safeExec (pre_dfs2 (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (vis2_l_low_level_spec) (sid_l_low_level_spec) (root_v_low_level_spec)) (dfs_scc (g_low_level_spec) (root_pre) (u_pre)) X_low_level_spec ) ” 
  &&  “ (0 <= u_pre) ” 
  &&  “ (u_pre < n_pre) ” 
  &&  “ (0 <= root_pre) ” 
  &&  “ (root_pre < n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ ((Znth (root_pre) (vis2_l_low_level_spec) (0)) <> 0) ”
  &&  (((vis2_pre + (u_pre * sizeof(INT) ) )) # Int  |->_)
  **  (IntArray.missing_i vis2_pre u_pre 0 n_pre vis2_l_low_level_spec )
  **  (IntArray.full fadj_col_pre (m_of (fadj_row_l_low_level_spec)) fadj_col_l_low_level_spec )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_low_level_spec )
  **  (IntArray.full sid_pre n_pre sid_l_low_level_spec )
.

Definition dfs2_partial_solve_wit_2 := 
forall (sid_pre: Z) (vis2_pre: Z) (fadj_row_pre: Z) (fadj_col_pre: Z) (n_pre: Z) (u_pre: Z) (root_pre: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (root_v_low_level_spec: Z) (sid_l_low_level_spec: (@list Z)) (vis2_l_low_level_spec: (@list Z)) (fadj_row_l_low_level_spec: (@list Z)) (fadj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (PreH1 : (csr_wf2 g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec vis2_l_low_level_spec sid_l_low_level_spec )) (PreH2 : (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH3 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH4 : (safeExec (pre_dfs2 (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (vis2_l_low_level_spec) (sid_l_low_level_spec) (root_v_low_level_spec)) (dfs_scc (g_low_level_spec) (root_pre) (u_pre)) X_low_level_spec )) (PreH5 : (0 <= u_pre)) (PreH6 : (u_pre < n_pre)) (PreH7 : (0 <= root_pre)) (PreH8 : (root_pre < n_pre)) (PreH9 : (n_pre <= INT_MAX)) (PreH10 : ((Znth (root_pre) (vis2_l_low_level_spec) (0)) <> 0)) ,
  (IntArray.full vis2_pre n_pre (replace_Znth (u_pre) (1) (vis2_l_low_level_spec)) )
  **  (IntArray.full fadj_col_pre (m_of (fadj_row_l_low_level_spec)) fadj_col_l_low_level_spec )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_low_level_spec )
  **  (IntArray.full sid_pre n_pre sid_l_low_level_spec )
|--
  “ (csr_wf2 g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec vis2_l_low_level_spec sid_l_low_level_spec ) ” 
  &&  “ (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec ) ” 
  &&  “ ((adj_verts (g_low_level_spec)) = n_pre) ” 
  &&  “ (safeExec (pre_dfs2 (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (vis2_l_low_level_spec) (sid_l_low_level_spec) (root_v_low_level_spec)) (dfs_scc (g_low_level_spec) (root_pre) (u_pre)) X_low_level_spec ) ” 
  &&  “ (0 <= u_pre) ” 
  &&  “ (u_pre < n_pre) ” 
  &&  “ (0 <= root_pre) ” 
  &&  “ (root_pre < n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ ((Znth (root_pre) (vis2_l_low_level_spec) (0)) <> 0) ”
  &&  (((sid_pre + (root_pre * sizeof(INT) ) )) # Int  |-> (Znth root_pre sid_l_low_level_spec 0))
  **  (IntArray.missing_i sid_pre root_pre 0 n_pre sid_l_low_level_spec )
  **  (IntArray.full vis2_pre n_pre (replace_Znth (u_pre) (1) (vis2_l_low_level_spec)) )
  **  (IntArray.full fadj_col_pre (m_of (fadj_row_l_low_level_spec)) fadj_col_l_low_level_spec )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_low_level_spec )
.

Definition dfs2_partial_solve_wit_3 := 
forall (sid_pre: Z) (vis2_pre: Z) (fadj_row_pre: Z) (fadj_col_pre: Z) (n_pre: Z) (u_pre: Z) (root_pre: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (root_v_low_level_spec: Z) (sid_l_low_level_spec: (@list Z)) (vis2_l_low_level_spec: (@list Z)) (fadj_row_l_low_level_spec: (@list Z)) (fadj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (PreH1 : (csr_wf2 g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec vis2_l_low_level_spec sid_l_low_level_spec )) (PreH2 : (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH3 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH4 : (safeExec (pre_dfs2 (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (vis2_l_low_level_spec) (sid_l_low_level_spec) (root_v_low_level_spec)) (dfs_scc (g_low_level_spec) (root_pre) (u_pre)) X_low_level_spec )) (PreH5 : (0 <= u_pre)) (PreH6 : (u_pre < n_pre)) (PreH7 : (0 <= root_pre)) (PreH8 : (root_pre < n_pre)) (PreH9 : (n_pre <= INT_MAX)) (PreH10 : ((Znth (root_pre) (vis2_l_low_level_spec) (0)) <> 0)) ,
  (IntArray.full sid_pre n_pre sid_l_low_level_spec )
  **  (IntArray.full vis2_pre n_pre (replace_Znth (u_pre) (1) (vis2_l_low_level_spec)) )
  **  (IntArray.full fadj_col_pre (m_of (fadj_row_l_low_level_spec)) fadj_col_l_low_level_spec )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_low_level_spec )
|--
  “ (csr_wf2 g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec vis2_l_low_level_spec sid_l_low_level_spec ) ” 
  &&  “ (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec ) ” 
  &&  “ ((adj_verts (g_low_level_spec)) = n_pre) ” 
  &&  “ (safeExec (pre_dfs2 (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (vis2_l_low_level_spec) (sid_l_low_level_spec) (root_v_low_level_spec)) (dfs_scc (g_low_level_spec) (root_pre) (u_pre)) X_low_level_spec ) ” 
  &&  “ (0 <= u_pre) ” 
  &&  “ (u_pre < n_pre) ” 
  &&  “ (0 <= root_pre) ” 
  &&  “ (root_pre < n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ ((Znth (root_pre) (vis2_l_low_level_spec) (0)) <> 0) ”
  &&  (((sid_pre + (u_pre * sizeof(INT) ) )) # Int  |->_)
  **  (IntArray.missing_i sid_pre u_pre 0 n_pre sid_l_low_level_spec )
  **  (IntArray.full vis2_pre n_pre (replace_Znth (u_pre) (1) (vis2_l_low_level_spec)) )
  **  (IntArray.full fadj_col_pre (m_of (fadj_row_l_low_level_spec)) fadj_col_l_low_level_spec )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_low_level_spec )
.

Definition dfs2_partial_solve_wit_4 := 
forall (sid_pre: Z) (vis2_pre: Z) (fadj_row_pre: Z) (fadj_col_pre: Z) (n_pre: Z) (u_pre: Z) (root_pre: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (root_v_low_level_spec: Z) (sid_l_low_level_spec: (@list Z)) (vis2_l_low_level_spec: (@list Z)) (fadj_row_l_low_level_spec: (@list Z)) (fadj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (PreH1 : (csr_wf2 g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec vis2_l_low_level_spec sid_l_low_level_spec )) (PreH2 : (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH3 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH4 : (safeExec (pre_dfs2 (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (vis2_l_low_level_spec) (sid_l_low_level_spec) (root_v_low_level_spec)) (dfs_scc (g_low_level_spec) (root_pre) (u_pre)) X_low_level_spec )) (PreH5 : (0 <= u_pre)) (PreH6 : (u_pre < n_pre)) (PreH7 : (0 <= root_pre)) (PreH8 : (root_pre < n_pre)) (PreH9 : (n_pre <= INT_MAX)) (PreH10 : ((Znth (root_pre) (vis2_l_low_level_spec) (0)) <> 0)) ,
  (IntArray.full sid_pre n_pre (replace_Znth (u_pre) ((Znth root_pre sid_l_low_level_spec 0)) (sid_l_low_level_spec)) )
  **  (IntArray.full vis2_pre n_pre (replace_Znth (u_pre) (1) (vis2_l_low_level_spec)) )
  **  (IntArray.full fadj_col_pre (m_of (fadj_row_l_low_level_spec)) fadj_col_l_low_level_spec )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_low_level_spec )
|--
  “ (csr_wf2 g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec vis2_l_low_level_spec sid_l_low_level_spec ) ” 
  &&  “ (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec ) ” 
  &&  “ ((adj_verts (g_low_level_spec)) = n_pre) ” 
  &&  “ (safeExec (pre_dfs2 (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (vis2_l_low_level_spec) (sid_l_low_level_spec) (root_v_low_level_spec)) (dfs_scc (g_low_level_spec) (root_pre) (u_pre)) X_low_level_spec ) ” 
  &&  “ (0 <= u_pre) ” 
  &&  “ (u_pre < n_pre) ” 
  &&  “ (0 <= root_pre) ” 
  &&  “ (root_pre < n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ ((Znth (root_pre) (vis2_l_low_level_spec) (0)) <> 0) ”
  &&  (((fadj_row_pre + (u_pre * sizeof(INT) ) )) # Int  |-> (Znth u_pre fadj_row_l_low_level_spec 0))
  **  (IntArray.missing_i fadj_row_pre u_pre 0 (n_pre + 1 ) fadj_row_l_low_level_spec )
  **  (IntArray.full sid_pre n_pre (replace_Znth (u_pre) ((Znth root_pre sid_l_low_level_spec 0)) (sid_l_low_level_spec)) )
  **  (IntArray.full vis2_pre n_pre (replace_Znth (u_pre) (1) (vis2_l_low_level_spec)) )
  **  (IntArray.full fadj_col_pre (m_of (fadj_row_l_low_level_spec)) fadj_col_l_low_level_spec )
.

Definition dfs2_partial_solve_wit_5 := 
forall (sid_pre: Z) (vis2_pre: Z) (fadj_row_pre: Z) (fadj_col_pre: Z) (n_pre: Z) (u_pre: Z) (root_pre: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (root_v_low_level_spec: Z) (sid_l_low_level_spec: (@list Z)) (vis2_l_low_level_spec: (@list Z)) (fadj_row_l_low_level_spec: (@list Z)) (fadj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (PreH1 : (csr_wf2 g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec vis2_l_low_level_spec sid_l_low_level_spec )) (PreH2 : (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH3 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH4 : (safeExec (pre_dfs2 (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (vis2_l_low_level_spec) (sid_l_low_level_spec) (root_v_low_level_spec)) (dfs_scc (g_low_level_spec) (root_pre) (u_pre)) X_low_level_spec )) (PreH5 : (0 <= u_pre)) (PreH6 : (u_pre < n_pre)) (PreH7 : (0 <= root_pre)) (PreH8 : (root_pre < n_pre)) (PreH9 : (n_pre <= INT_MAX)) (PreH10 : ((Znth (root_pre) (vis2_l_low_level_spec) (0)) <> 0)) ,
  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_low_level_spec )
  **  (IntArray.full sid_pre n_pre (replace_Znth (u_pre) ((Znth root_pre sid_l_low_level_spec 0)) (sid_l_low_level_spec)) )
  **  (IntArray.full vis2_pre n_pre (replace_Znth (u_pre) (1) (vis2_l_low_level_spec)) )
  **  (IntArray.full fadj_col_pre (m_of (fadj_row_l_low_level_spec)) fadj_col_l_low_level_spec )
|--
  “ (csr_wf2 g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec vis2_l_low_level_spec sid_l_low_level_spec ) ” 
  &&  “ (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec ) ” 
  &&  “ ((adj_verts (g_low_level_spec)) = n_pre) ” 
  &&  “ (safeExec (pre_dfs2 (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (vis2_l_low_level_spec) (sid_l_low_level_spec) (root_v_low_level_spec)) (dfs_scc (g_low_level_spec) (root_pre) (u_pre)) X_low_level_spec ) ” 
  &&  “ (0 <= u_pre) ” 
  &&  “ (u_pre < n_pre) ” 
  &&  “ (0 <= root_pre) ” 
  &&  “ (root_pre < n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ ((Znth (root_pre) (vis2_l_low_level_spec) (0)) <> 0) ”
  &&  (((fadj_row_pre + ((u_pre + 1 ) * sizeof(INT) ) )) # Int  |-> (Znth (u_pre + 1 ) fadj_row_l_low_level_spec 0))
  **  (IntArray.missing_i fadj_row_pre (u_pre + 1 ) 0 (n_pre + 1 ) fadj_row_l_low_level_spec )
  **  (IntArray.full sid_pre n_pre (replace_Znth (u_pre) ((Znth root_pre sid_l_low_level_spec 0)) (sid_l_low_level_spec)) )
  **  (IntArray.full vis2_pre n_pre (replace_Znth (u_pre) (1) (vis2_l_low_level_spec)) )
  **  (IntArray.full fadj_col_pre (m_of (fadj_row_l_low_level_spec)) fadj_col_l_low_level_spec )
.

Definition dfs2_partial_solve_wit_6 := 
forall (sid_pre: Z) (vis2_pre: Z) (fadj_row_pre: Z) (fadj_col_pre: Z) (n_pre: Z) (u_pre: Z) (root_pre: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (root_v_low_level_spec: Z) (vis2_l_low_level_spec: (@list Z)) (fadj_row_l_low_level_spec: (@list Z)) (fadj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (hi: Z) (lo: Z) (i: Z) (vis2_m: (@list Z)) (sid_m: (@list Z)) (PreH1 : (i < hi)) (PreH2 : (csr_wf2 g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec vis2_m sid_m )) (PreH3 : (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH4 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH5 : (safeExec (pre_dfs2 (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (vis2_m) (sid_m) (root_v_low_level_spec)) (dfs_scc_from (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (root_pre) (u_pre) (i)) X_low_level_spec )) (PreH6 : (lo = (csr_lo (u_pre) (fadj_row_l_low_level_spec)))) (PreH7 : (hi = (csr_hi (u_pre) (fadj_row_l_low_level_spec)))) (PreH8 : (0 <= lo)) (PreH9 : (lo <= i)) (PreH10 : (i <= hi)) (PreH11 : (hi <= (m_of (fadj_row_l_low_level_spec)))) (PreH12 : (0 <= u_pre)) (PreH13 : (u_pre < n_pre)) (PreH14 : (0 <= root_pre)) (PreH15 : (root_pre < n_pre)) (PreH16 : (n_pre <= INT_MAX)) (PreH17 : ((Znth (u_pre) (vis2_m) (0)) <> 0)) (PreH18 : forall (j: Z) , (((lo <= j) /\ (j < i)) -> ((Znth ((Znth (j) (fadj_col_l_low_level_spec) (0))) (vis2_m) (0)) <> 0))) (PreH19 : ((Znth (root_pre) (vis2_m) (0)) <> 0)) (PreH20 : forall (w: Z) , (((0 <= w) /\ (w < n_pre)) -> (((Znth (w) (vis2_l_low_level_spec) (0)) <> 0) -> ((Znth (w) (vis2_m) (0)) <> 0)))) ,
  (IntArray.full fadj_col_pre (m_of (fadj_row_l_low_level_spec)) fadj_col_l_low_level_spec )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_low_level_spec )
  **  (IntArray.full vis2_pre n_pre vis2_m )
  **  (IntArray.full sid_pre n_pre sid_m )
|--
  “ (i < hi) ” 
  &&  “ (csr_wf2 g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec vis2_m sid_m ) ” 
  &&  “ (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec ) ” 
  &&  “ ((adj_verts (g_low_level_spec)) = n_pre) ” 
  &&  “ (safeExec (pre_dfs2 (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (vis2_m) (sid_m) (root_v_low_level_spec)) (dfs_scc_from (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (root_pre) (u_pre) (i)) X_low_level_spec ) ” 
  &&  “ (lo = (csr_lo (u_pre) (fadj_row_l_low_level_spec))) ” 
  &&  “ (hi = (csr_hi (u_pre) (fadj_row_l_low_level_spec))) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= i) ” 
  &&  “ (i <= hi) ” 
  &&  “ (hi <= (m_of (fadj_row_l_low_level_spec))) ” 
  &&  “ (0 <= u_pre) ” 
  &&  “ (u_pre < n_pre) ” 
  &&  “ (0 <= root_pre) ” 
  &&  “ (root_pre < n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ ((Znth (u_pre) (vis2_m) (0)) <> 0) ” 
  &&  “ forall (j: Z) , (((lo <= j) /\ (j < i)) -> ((Znth ((Znth (j) (fadj_col_l_low_level_spec) (0))) (vis2_m) (0)) <> 0)) ” 
  &&  “ ((Znth (root_pre) (vis2_m) (0)) <> 0) ” 
  &&  “ forall (w: Z) , (((0 <= w) /\ (w < n_pre)) -> (((Znth (w) (vis2_l_low_level_spec) (0)) <> 0) -> ((Znth (w) (vis2_m) (0)) <> 0))) ”
  &&  (((fadj_col_pre + (i * sizeof(INT) ) )) # Int  |-> (Znth i fadj_col_l_low_level_spec 0))
  **  (IntArray.missing_i fadj_col_pre i 0 (m_of (fadj_row_l_low_level_spec)) fadj_col_l_low_level_spec )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_low_level_spec )
  **  (IntArray.full vis2_pre n_pre vis2_m )
  **  (IntArray.full sid_pre n_pre sid_m )
.

Definition dfs2_partial_solve_wit_7 := 
forall (sid_pre: Z) (vis2_pre: Z) (fadj_row_pre: Z) (fadj_col_pre: Z) (n_pre: Z) (u_pre: Z) (root_pre: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (root_v_low_level_spec: Z) (vis2_l_low_level_spec: (@list Z)) (fadj_row_l_low_level_spec: (@list Z)) (fadj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (vis2_m: (@list Z)) (sid_m: (@list Z)) (i: Z) (lo: Z) (hi: Z) (v: Z) (PreH1 : (csr_wf2 g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec vis2_m sid_m )) (PreH2 : (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH3 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH4 : (safeExec (pre_dfs2 (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (vis2_m) (sid_m) (root_v_low_level_spec)) (dfs_scc_from (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (root_pre) (u_pre) (i)) X_low_level_spec )) (PreH5 : (lo = (csr_lo (u_pre) (fadj_row_l_low_level_spec)))) (PreH6 : (hi = (csr_hi (u_pre) (fadj_row_l_low_level_spec)))) (PreH7 : (0 <= lo)) (PreH8 : (lo <= i)) (PreH9 : (i < hi)) (PreH10 : (hi <= (m_of (fadj_row_l_low_level_spec)))) (PreH11 : (0 <= u_pre)) (PreH12 : (u_pre < n_pre)) (PreH13 : (0 <= root_pre)) (PreH14 : (root_pre < n_pre)) (PreH15 : (n_pre <= INT_MAX)) (PreH16 : ((Znth (u_pre) (vis2_m) (0)) <> 0)) (PreH17 : forall (j: Z) , (((lo <= j) /\ (j < i)) -> ((Znth ((Znth (j) (fadj_col_l_low_level_spec) (0))) (vis2_m) (0)) <> 0))) (PreH18 : ((Znth (root_pre) (vis2_m) (0)) <> 0)) (PreH19 : forall (w: Z) , (((0 <= w) /\ (w < n_pre)) -> (((Znth (w) (vis2_l_low_level_spec) (0)) <> 0) -> ((Znth (w) (vis2_m) (0)) <> 0)))) (PreH20 : (0 <= v)) (PreH21 : (v < n_pre)) (PreH22 : (v = (Znth (i) (fadj_col_l_low_level_spec) (0)))) ,
  (IntArray.full fadj_col_pre (m_of (fadj_row_l_low_level_spec)) fadj_col_l_low_level_spec )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_low_level_spec )
  **  (IntArray.full vis2_pre n_pre vis2_m )
  **  (IntArray.full sid_pre n_pre sid_m )
|--
  “ (csr_wf2 g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec vis2_m sid_m ) ” 
  &&  “ (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec ) ” 
  &&  “ ((adj_verts (g_low_level_spec)) = n_pre) ” 
  &&  “ (safeExec (pre_dfs2 (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (vis2_m) (sid_m) (root_v_low_level_spec)) (dfs_scc_from (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (root_pre) (u_pre) (i)) X_low_level_spec ) ” 
  &&  “ (lo = (csr_lo (u_pre) (fadj_row_l_low_level_spec))) ” 
  &&  “ (hi = (csr_hi (u_pre) (fadj_row_l_low_level_spec))) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= i) ” 
  &&  “ (i < hi) ” 
  &&  “ (hi <= (m_of (fadj_row_l_low_level_spec))) ” 
  &&  “ (0 <= u_pre) ” 
  &&  “ (u_pre < n_pre) ” 
  &&  “ (0 <= root_pre) ” 
  &&  “ (root_pre < n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ ((Znth (u_pre) (vis2_m) (0)) <> 0) ” 
  &&  “ forall (j: Z) , (((lo <= j) /\ (j < i)) -> ((Znth ((Znth (j) (fadj_col_l_low_level_spec) (0))) (vis2_m) (0)) <> 0)) ” 
  &&  “ ((Znth (root_pre) (vis2_m) (0)) <> 0) ” 
  &&  “ forall (w: Z) , (((0 <= w) /\ (w < n_pre)) -> (((Znth (w) (vis2_l_low_level_spec) (0)) <> 0) -> ((Znth (w) (vis2_m) (0)) <> 0))) ” 
  &&  “ (0 <= v) ” 
  &&  “ (v < n_pre) ” 
  &&  “ (v = (Znth (i) (fadj_col_l_low_level_spec) (0))) ”
  &&  (((vis2_pre + (v * sizeof(INT) ) )) # Int  |-> (Znth v vis2_m 0))
  **  (IntArray.missing_i vis2_pre v 0 n_pre vis2_m )
  **  (IntArray.full fadj_col_pre (m_of (fadj_row_l_low_level_spec)) fadj_col_l_low_level_spec )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_low_level_spec )
  **  (IntArray.full sid_pre n_pre sid_m )
.

Definition dfs2_partial_solve_wit_8_pure := 
(
forall (sid_pre: Z) (vis2_pre: Z) (fadj_row_pre: Z) (fadj_col_pre: Z) (n_pre: Z) (u_pre: Z) (root_pre: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (root_v_low_level_spec: Z) (vis2_l_low_level_spec: (@list Z)) (fadj_row_l_low_level_spec: (@list Z)) (fadj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (vis2_m: (@list Z)) (sid_m: (@list Z)) (i: Z) (lo: Z) (hi: Z) (v: Z) (PreH1 : ((Znth v vis2_m 0) = 0)) (PreH2 : (csr_wf2 g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec vis2_m sid_m )) (PreH3 : (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH4 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH5 : (safeExec (pre_dfs2 (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (vis2_m) (sid_m) (root_v_low_level_spec)) (dfs_scc_from (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (root_pre) (u_pre) (i)) X_low_level_spec )) (PreH6 : (lo = (csr_lo (u_pre) (fadj_row_l_low_level_spec)))) (PreH7 : (hi = (csr_hi (u_pre) (fadj_row_l_low_level_spec)))) (PreH8 : (0 <= lo)) (PreH9 : (lo <= i)) (PreH10 : (i < hi)) (PreH11 : (hi <= (m_of (fadj_row_l_low_level_spec)))) (PreH12 : (0 <= u_pre)) (PreH13 : (u_pre < n_pre)) (PreH14 : (0 <= root_pre)) (PreH15 : (root_pre < n_pre)) (PreH16 : (n_pre <= INT_MAX)) (PreH17 : ((Znth (u_pre) (vis2_m) (0)) <> 0)) (PreH18 : forall (j: Z) , (((lo <= j) /\ (j < i)) -> ((Znth ((Znth (j) (fadj_col_l_low_level_spec) (0))) (vis2_m) (0)) <> 0))) (PreH19 : ((Znth (root_pre) (vis2_m) (0)) <> 0)) (PreH20 : forall (w: Z) , (((0 <= w) /\ (w < n_pre)) -> (((Znth (w) (vis2_l_low_level_spec) (0)) <> 0) -> ((Znth (w) (vis2_m) (0)) <> 0)))) (PreH21 : (0 <= v)) (PreH22 : (v < n_pre)) (PreH23 : (v = (Znth (i) (fadj_col_l_low_level_spec) (0)))) ,
  (IntArray.full vis2_pre n_pre vis2_m )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "u" ) )) # Int  |-> u_pre)
  **  ((( &( "root" ) )) # Int  |-> root_pre)
  **  ((( &( "fadj_col" ) )) # Ptr  |-> fadj_col_pre)
  **  ((( &( "fadj_row" ) )) # Ptr  |-> fadj_row_pre)
  **  ((( &( "vis2" ) )) # Ptr  |-> vis2_pre)
  **  ((( &( "sid" ) )) # Ptr  |-> sid_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  (IntArray.full fadj_col_pre (m_of (fadj_row_l_low_level_spec)) fadj_col_l_low_level_spec )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_low_level_spec )
  **  (IntArray.full sid_pre n_pre sid_m )
|--
  “ (csr_wf2 g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec vis2_m sid_m ) ” 
  &&  “ (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec ) ” 
  &&  “ ((adj_verts (g_low_level_spec)) = n_pre) ” 
  &&  “ (0 <= v) ” 
  &&  “ (v < n_pre) ” 
  &&  “ (0 <= root_pre) ” 
  &&  “ (root_pre < n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ ((Znth (root_pre) (vis2_m) (0)) <> 0) ” 
  &&  “ (safeExec (pre_dfs2 (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (vis2_m) (sid_m) (root_v_low_level_spec)) (bind ((dfs_scc (g_low_level_spec) (root_pre) (v))) ((dfs_scc_fromK (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (root_pre) (u_pre) ((i + 1 ))))) X_low_level_spec ) ”
) \/
(
forall (sid_pre: Z) (vis2_pre: Z) (fadj_row_pre: Z) (fadj_col_pre: Z) (n_pre: Z) (u_pre: Z) (root_pre: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (root_v_low_level_spec: Z) (vis2_l_low_level_spec: (@list Z)) (fadj_row_l_low_level_spec: (@list Z)) (fadj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (vis2_m: (@list Z)) (sid_m: (@list Z)) (i: Z) (lo: Z) (hi: Z) (v: Z) (PreH1 : (v <= INT_MAX)) (PreH2 : (hi <= INT_MAX)) (PreH3 : (lo <= INT_MAX)) (PreH4 : (root_pre <= INT_MAX)) (PreH5 : (u_pre <= INT_MAX)) (PreH6 : (i <= INT_MAX)) (PreH7 : (n_pre <= INT_MAX)) (PreH8 : (v >= INT_MIN)) (PreH9 : (hi >= INT_MIN)) (PreH10 : (lo >= INT_MIN)) (PreH11 : (root_pre >= INT_MIN)) (PreH12 : (u_pre >= INT_MIN)) (PreH13 : (i >= INT_MIN)) (PreH14 : (n_pre >= INT_MIN)) (PreH15 : ((Znth v vis2_m 0) = 0)) (PreH16 : (csr_wf2 g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec vis2_m sid_m )) (PreH17 : (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH18 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH19 : (safeExec (pre_dfs2 (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (vis2_m) (sid_m) (root_v_low_level_spec)) (dfs_scc_from (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (root_pre) (u_pre) (i)) X_low_level_spec )) (PreH20 : (lo = (csr_lo (u_pre) (fadj_row_l_low_level_spec)))) (PreH21 : (hi = (csr_hi (u_pre) (fadj_row_l_low_level_spec)))) (PreH22 : (0 <= lo)) (PreH23 : (lo <= i)) (PreH24 : (i < hi)) (PreH25 : (hi <= (m_of (fadj_row_l_low_level_spec)))) (PreH26 : (0 <= u_pre)) (PreH27 : (u_pre < n_pre)) (PreH28 : (0 <= root_pre)) (PreH29 : (root_pre < n_pre)) (PreH30 : (n_pre <= INT_MAX)) (PreH31 : ((Znth (u_pre) (vis2_m) (0)) <> 0)) (PreH32 : forall (j: Z) , (((lo <= j) /\ (j < i)) -> ((Znth ((Znth (j) (fadj_col_l_low_level_spec) (0))) (vis2_m) (0)) <> 0))) (PreH33 : ((Znth (root_pre) (vis2_m) (0)) <> 0)) (PreH34 : forall (w: Z) , (((0 <= w) /\ (w < n_pre)) -> (((Znth (w) (vis2_l_low_level_spec) (0)) <> 0) -> ((Znth (w) (vis2_m) (0)) <> 0)))) (PreH35 : (0 <= v)) (PreH36 : (v < n_pre)) (PreH37 : (v = (Znth (i) (fadj_col_l_low_level_spec) (0)))) ,
  (IntArray.full vis2_pre n_pre vis2_m )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "u" ) )) # Int  |-> u_pre)
  **  ((( &( "root" ) )) # Int  |-> root_pre)
  **  ((( &( "fadj_col" ) )) # Ptr  |-> fadj_col_pre)
  **  ((( &( "fadj_row" ) )) # Ptr  |-> fadj_row_pre)
  **  ((( &( "vis2" ) )) # Ptr  |-> vis2_pre)
  **  ((( &( "sid" ) )) # Ptr  |-> sid_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  (IntArray.full fadj_col_pre (m_of (fadj_row_l_low_level_spec)) fadj_col_l_low_level_spec )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_low_level_spec )
  **  (IntArray.full sid_pre n_pre sid_m )
|--
  “ (safeExec (pre_dfs2 (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (vis2_m) (sid_m) (root_v_low_level_spec)) (bind ((dfs_scc (g_low_level_spec) (root_pre) (v))) ((dfs_scc_fromK (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (root_pre) (u_pre) ((i + 1 ))))) X_low_level_spec ) ”
).

Definition dfs2_partial_solve_wit_8_pure_split_goal_1 := 
forall (sid_pre: Z) (vis2_pre: Z) (fadj_row_pre: Z) (fadj_col_pre: Z) (n_pre: Z) (u_pre: Z) (root_pre: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (root_v_low_level_spec: Z) (vis2_l_low_level_spec: (@list Z)) (fadj_row_l_low_level_spec: (@list Z)) (fadj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (vis2_m: (@list Z)) (sid_m: (@list Z)) (i: Z) (lo: Z) (hi: Z) (v: Z) (PreH1 : (v <= INT_MAX)) (PreH2 : (hi <= INT_MAX)) (PreH3 : (lo <= INT_MAX)) (PreH4 : (root_pre <= INT_MAX)) (PreH5 : (u_pre <= INT_MAX)) (PreH6 : (i <= INT_MAX)) (PreH7 : (n_pre <= INT_MAX)) (PreH8 : (v >= INT_MIN)) (PreH9 : (hi >= INT_MIN)) (PreH10 : (lo >= INT_MIN)) (PreH11 : (root_pre >= INT_MIN)) (PreH12 : (u_pre >= INT_MIN)) (PreH13 : (i >= INT_MIN)) (PreH14 : (n_pre >= INT_MIN)) (PreH15 : ((Znth v vis2_m 0) = 0)) (PreH16 : (csr_wf2 g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec vis2_m sid_m )) (PreH17 : (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH18 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH19 : (safeExec (pre_dfs2 (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (vis2_m) (sid_m) (root_v_low_level_spec)) (dfs_scc_from (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (root_pre) (u_pre) (i)) X_low_level_spec )) (PreH20 : (lo = (csr_lo (u_pre) (fadj_row_l_low_level_spec)))) (PreH21 : (hi = (csr_hi (u_pre) (fadj_row_l_low_level_spec)))) (PreH22 : (0 <= lo)) (PreH23 : (lo <= i)) (PreH24 : (i < hi)) (PreH25 : (hi <= (m_of (fadj_row_l_low_level_spec)))) (PreH26 : (0 <= u_pre)) (PreH27 : (u_pre < n_pre)) (PreH28 : (0 <= root_pre)) (PreH29 : (root_pre < n_pre)) (PreH30 : (n_pre <= INT_MAX)) (PreH31 : ((Znth (u_pre) (vis2_m) (0)) <> 0)) (PreH32 : forall (j: Z) , (((lo <= j) /\ (j < i)) -> ((Znth ((Znth (j) (fadj_col_l_low_level_spec) (0))) (vis2_m) (0)) <> 0))) (PreH33 : ((Znth (root_pre) (vis2_m) (0)) <> 0)) (PreH34 : forall (w: Z) , (((0 <= w) /\ (w < n_pre)) -> (((Znth (w) (vis2_l_low_level_spec) (0)) <> 0) -> ((Znth (w) (vis2_m) (0)) <> 0)))) (PreH35 : (0 <= v)) (PreH36 : (v < n_pre)) (PreH37 : (v = (Znth (i) (fadj_col_l_low_level_spec) (0)))) ,
  (IntArray.full vis2_pre n_pre vis2_m )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "u" ) )) # Int  |-> u_pre)
  **  ((( &( "root" ) )) # Int  |-> root_pre)
  **  ((( &( "fadj_col" ) )) # Ptr  |-> fadj_col_pre)
  **  ((( &( "fadj_row" ) )) # Ptr  |-> fadj_row_pre)
  **  ((( &( "vis2" ) )) # Ptr  |-> vis2_pre)
  **  ((( &( "sid" ) )) # Ptr  |-> sid_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  (IntArray.full fadj_col_pre (m_of (fadj_row_l_low_level_spec)) fadj_col_l_low_level_spec )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_low_level_spec )
  **  (IntArray.full sid_pre n_pre sid_m )
|--
  “ (safeExec (pre_dfs2 (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (vis2_m) (sid_m) (root_v_low_level_spec)) (bind ((dfs_scc (g_low_level_spec) (root_pre) (v))) ((dfs_scc_fromK (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (root_pre) (u_pre) ((i + 1 ))))) X_low_level_spec ) ”
.

Definition dfs2_partial_solve_wit_8_aux := 
forall (sid_pre: Z) (vis2_pre: Z) (fadj_row_pre: Z) (fadj_col_pre: Z) (n_pre: Z) (u_pre: Z) (root_pre: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) (root_v_low_level_spec: Z) (vis2_l_low_level_spec: (@list Z)) (fadj_row_l_low_level_spec: (@list Z)) (fadj_col_l_low_level_spec: (@list Z)) (g_low_level_spec: AdjGraph) (vis2_m: (@list Z)) (sid_m: (@list Z)) (i: Z) (lo: Z) (hi: Z) (v: Z) (PreH1 : ((Znth v vis2_m 0) = 0)) (PreH2 : (csr_wf2 g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec vis2_m sid_m )) (PreH3 : (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec )) (PreH4 : ((adj_verts (g_low_level_spec)) = n_pre)) (PreH5 : (safeExec (pre_dfs2 (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (vis2_m) (sid_m) (root_v_low_level_spec)) (dfs_scc_from (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (root_pre) (u_pre) (i)) X_low_level_spec )) (PreH6 : (lo = (csr_lo (u_pre) (fadj_row_l_low_level_spec)))) (PreH7 : (hi = (csr_hi (u_pre) (fadj_row_l_low_level_spec)))) (PreH8 : (0 <= lo)) (PreH9 : (lo <= i)) (PreH10 : (i < hi)) (PreH11 : (hi <= (m_of (fadj_row_l_low_level_spec)))) (PreH12 : (0 <= u_pre)) (PreH13 : (u_pre < n_pre)) (PreH14 : (0 <= root_pre)) (PreH15 : (root_pre < n_pre)) (PreH16 : (n_pre <= INT_MAX)) (PreH17 : ((Znth (u_pre) (vis2_m) (0)) <> 0)) (PreH18 : forall (j: Z) , (((lo <= j) /\ (j < i)) -> ((Znth ((Znth (j) (fadj_col_l_low_level_spec) (0))) (vis2_m) (0)) <> 0))) (PreH19 : ((Znth (root_pre) (vis2_m) (0)) <> 0)) (PreH20 : forall (w: Z) , (((0 <= w) /\ (w < n_pre)) -> (((Znth (w) (vis2_l_low_level_spec) (0)) <> 0) -> ((Znth (w) (vis2_m) (0)) <> 0)))) (PreH21 : (0 <= v)) (PreH22 : (v < n_pre)) (PreH23 : (v = (Znth (i) (fadj_col_l_low_level_spec) (0)))) ,
  (IntArray.full vis2_pre n_pre vis2_m )
  **  (IntArray.full fadj_col_pre (m_of (fadj_row_l_low_level_spec)) fadj_col_l_low_level_spec )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_low_level_spec )
  **  (IntArray.full sid_pre n_pre sid_m )
|--
  “ (csr_wf2 g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec vis2_m sid_m ) ” 
  &&  “ (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec ) ” 
  &&  “ ((adj_verts (g_low_level_spec)) = n_pre) ” 
  &&  “ (0 <= v) ” 
  &&  “ (v < n_pre) ” 
  &&  “ (0 <= root_pre) ” 
  &&  “ (root_pre < n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ ((Znth (root_pre) (vis2_m) (0)) <> 0) ” 
  &&  “ (safeExec (pre_dfs2 (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (vis2_m) (sid_m) (root_v_low_level_spec)) (bind ((dfs_scc (g_low_level_spec) (root_pre) (v))) ((dfs_scc_fromK (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (root_pre) (u_pre) ((i + 1 ))))) X_low_level_spec ) ” 
  &&  “ ((Znth v vis2_m 0) = 0) ” 
  &&  “ (csr_wf2 g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec vis2_m sid_m ) ” 
  &&  “ (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec ) ” 
  &&  “ ((adj_verts (g_low_level_spec)) = n_pre) ” 
  &&  “ (safeExec (pre_dfs2 (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (vis2_m) (sid_m) (root_v_low_level_spec)) (dfs_scc_from (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (root_pre) (u_pre) (i)) X_low_level_spec ) ” 
  &&  “ (lo = (csr_lo (u_pre) (fadj_row_l_low_level_spec))) ” 
  &&  “ (hi = (csr_hi (u_pre) (fadj_row_l_low_level_spec))) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= i) ” 
  &&  “ (i < hi) ” 
  &&  “ (hi <= (m_of (fadj_row_l_low_level_spec))) ” 
  &&  “ (0 <= u_pre) ” 
  &&  “ (u_pre < n_pre) ” 
  &&  “ (0 <= root_pre) ” 
  &&  “ (root_pre < n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ ((Znth (u_pre) (vis2_m) (0)) <> 0) ” 
  &&  “ forall (j: Z) , (((lo <= j) /\ (j < i)) -> ((Znth ((Znth (j) (fadj_col_l_low_level_spec) (0))) (vis2_m) (0)) <> 0)) ” 
  &&  “ ((Znth (root_pre) (vis2_m) (0)) <> 0) ” 
  &&  “ forall (w: Z) , (((0 <= w) /\ (w < n_pre)) -> (((Znth (w) (vis2_l_low_level_spec) (0)) <> 0) -> ((Znth (w) (vis2_m) (0)) <> 0))) ” 
  &&  “ (0 <= v) ” 
  &&  “ (v < n_pre) ” 
  &&  “ (v = (Znth (i) (fadj_col_l_low_level_spec) (0))) ”
  &&  (IntArray.full fadj_col_pre (m_of (fadj_row_l_low_level_spec)) fadj_col_l_low_level_spec )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_low_level_spec )
  **  (IntArray.full vis2_pre n_pre vis2_m )
  **  (IntArray.full sid_pre n_pre sid_m )
.

Definition dfs2_partial_solve_wit_8 := dfs2_partial_solve_wit_8_pure -> dfs2_partial_solve_wit_8_aux.

Definition dfs2_derive_bind_spec_by_low_level_spec := 
forall (B: Type) ,
forall (sid_pre: Z) (vis2_pre: Z) (fadj_row_pre: Z) (fadj_col_pre: Z) (n_pre: Z) (u_pre: Z) (root_pre: Z) (f_bind_spec: (unit -> (@ MonadErr.M  KSt B))) (X_bind_spec: (B -> (KSt -> Prop))) (root_v_bind_spec: Z) (sid_l_bind_spec: (@list Z)) (vis2_l_bind_spec: (@list Z)) (fadj_row_l_bind_spec: (@list Z)) (fadj_col_l_bind_spec: (@list Z)) (g_bind_spec: AdjGraph) ,
  “ (csr_wf2 g_bind_spec fadj_col_l_bind_spec fadj_row_l_bind_spec vis2_l_bind_spec sid_l_bind_spec ) ” 
  &&  “ (csr2_faithful g_bind_spec fadj_col_l_bind_spec fadj_row_l_bind_spec ) ” 
  &&  “ ((adj_verts (g_bind_spec)) = n_pre) ” 
  &&  “ (safeExec (pre_dfs2 (g_bind_spec) (fadj_col_l_bind_spec) (fadj_row_l_bind_spec) (vis2_l_bind_spec) (sid_l_bind_spec) (root_v_bind_spec)) (bind ((dfs_scc (g_bind_spec) (root_pre) (u_pre))) (f_bind_spec)) X_bind_spec ) ” 
  &&  “ (0 <= u_pre) ” 
  &&  “ (u_pre < n_pre) ” 
  &&  “ (0 <= root_pre) ” 
  &&  “ (root_pre < n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ ((Znth (root_pre) (vis2_l_bind_spec) (0)) <> 0) ”
  &&  (IntArray.full fadj_col_pre (m_of (fadj_row_l_bind_spec)) fadj_col_l_bind_spec )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_bind_spec )
  **  (IntArray.full vis2_pre n_pre vis2_l_bind_spec )
  **  (IntArray.full sid_pre n_pre sid_l_bind_spec )
|--
EX (g_low_level_spec: AdjGraph) (fadj_col_l_low_level_spec: (@list Z)) (fadj_row_l_low_level_spec: (@list Z)) (vis2_l_low_level_spec: (@list Z)) (sid_l_low_level_spec: (@list Z)) (root_v_low_level_spec: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) ,
  (“ (csr_wf2 g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec vis2_l_low_level_spec sid_l_low_level_spec ) ” 
  &&  “ (csr2_faithful g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec ) ” 
  &&  “ ((adj_verts (g_low_level_spec)) = n_pre) ” 
  &&  “ (safeExec (pre_dfs2 (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (vis2_l_low_level_spec) (sid_l_low_level_spec) (root_v_low_level_spec)) (dfs_scc (g_low_level_spec) (root_pre) (u_pre)) X_low_level_spec ) ” 
  &&  “ (0 <= u_pre) ” 
  &&  “ (u_pre < n_pre) ” 
  &&  “ (0 <= root_pre) ” 
  &&  “ (root_pre < n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ ((Znth (root_pre) (vis2_l_low_level_spec) (0)) <> 0) ”
  &&  (IntArray.full fadj_col_pre (m_of (fadj_row_l_low_level_spec)) fadj_col_l_low_level_spec )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_low_level_spec )
  **  (IntArray.full vis2_pre n_pre vis2_l_low_level_spec )
  **  (IntArray.full sid_pre n_pre sid_l_low_level_spec ))
  **
  ((EX vis2_l__2 sid_l__2,
  “ (csr_wf2 g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec vis2_l__2 sid_l__2 ) ” 
  &&  “ ((adj_verts (g_low_level_spec)) = n_pre) ” 
  &&  “ (safeExec (pre_dfs2 (g_low_level_spec) (fadj_col_l_low_level_spec) (fadj_row_l_low_level_spec) (vis2_l__2) (sid_l__2) (root_v_low_level_spec)) (return (tt)) X_low_level_spec ) ” 
  &&  “ ((Znth (u_pre) (vis2_l__2) (0)) <> 0) ” 
  &&  “ forall (w_2: Z) , (((0 <= w_2) /\ (w_2 < n_pre)) -> (((Znth (w_2) (vis2_l_low_level_spec) (0)) <> 0) -> ((Znth (w_2) (vis2_l__2) (0)) <> 0))) ”
  &&  (IntArray.full fadj_col_pre (m_of (fadj_row_l_low_level_spec)) fadj_col_l_low_level_spec )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_low_level_spec )
  **  (IntArray.full vis2_pre n_pre vis2_l__2 )
  **  (IntArray.full sid_pre n_pre sid_l__2 ))
  -*
  (EX vis2_l_ sid_l_,
  “ (csr_wf2 g_bind_spec fadj_col_l_bind_spec fadj_row_l_bind_spec vis2_l_ sid_l_ ) ” 
  &&  “ ((adj_verts (g_bind_spec)) = n_pre) ” 
  &&  “ (safeExec (pre_dfs2 (g_bind_spec) (fadj_col_l_bind_spec) (fadj_row_l_bind_spec) (vis2_l_) (sid_l_) (root_v_bind_spec)) (applyf (f_bind_spec) (tt)) X_bind_spec ) ” 
  &&  “ ((Znth (u_pre) (vis2_l_) (0)) <> 0) ” 
  &&  “ forall (w: Z) , (((0 <= w) /\ (w < n_pre)) -> (((Znth (w) (vis2_l_bind_spec) (0)) <> 0) -> ((Znth (w) (vis2_l_) (0)) <> 0))) ”
  &&  (IntArray.full fadj_col_pre (m_of (fadj_row_l_bind_spec)) fadj_col_l_bind_spec )
  **  (IntArray.full fadj_row_pre (n_pre + 1 ) fadj_row_l_bind_spec )
  **  (IntArray.full vis2_pre n_pre vis2_l_ )
  **  (IntArray.full sid_pre n_pre sid_l_ )))
.

Definition dfs1_derive_bind_spec_by_low_level_spec := 
forall (B: Type) ,
forall (timer_p_pre: Z) (fin_pre: Z) (vis1_pre: Z) (radj_row_pre: Z) (radj_col_pre: Z) (n_pre: Z) (u_pre: Z) (f_bind_spec: (unit -> (@ MonadErr.M  KSt B))) (X_bind_spec: (B -> (KSt -> Prop))) (timer_v_bind_spec: Z) (fin_l_bind_spec: (@list Z)) (vis1_l_bind_spec: (@list Z)) (radj_row_l_bind_spec: (@list Z)) (radj_col_l_bind_spec: (@list Z)) (g_bind_spec: AdjGraph) ,
  “ (csr_wf1 g_bind_spec radj_col_l_bind_spec radj_row_l_bind_spec vis1_l_bind_spec fin_l_bind_spec ) ” 
  &&  “ ((adj_verts (g_bind_spec)) = n_pre) ” 
  &&  “ (safeExec (pre_dfs1 (g_bind_spec) (radj_col_l_bind_spec) (radj_row_l_bind_spec) (vis1_l_bind_spec) (fin_l_bind_spec) (timer_v_bind_spec)) (bind ((dfs_finish (g_bind_spec) (u_pre))) (f_bind_spec)) X_bind_spec ) ” 
  &&  “ (0 <= u_pre) ” 
  &&  “ (u_pre < n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ ((Znth (u_pre) (vis1_l_bind_spec) (0)) = 0) ” 
  &&  “ (0 <= timer_v_bind_spec) ” 
  &&  “ (timer_v_bind_spec <= (count_nonzero (vis1_l_bind_spec))) ”
  &&  (IntArray.full radj_col_pre (m_of (radj_row_l_bind_spec)) radj_col_l_bind_spec )
  **  (IntArray.full radj_row_pre (n_pre + 1 ) radj_row_l_bind_spec )
  **  (IntArray.full vis1_pre n_pre vis1_l_bind_spec )
  **  (IntArray.full fin_pre n_pre fin_l_bind_spec )
  **  (IntArray.full timer_p_pre 1 (cons (timer_v_bind_spec) (nil)) )
|--
EX (g_low_level_spec: AdjGraph) (radj_col_l_low_level_spec: (@list Z)) (radj_row_l_low_level_spec: (@list Z)) (vis1_l_low_level_spec: (@list Z)) (fin_l_low_level_spec: (@list Z)) (timer_v_low_level_spec: Z) (X_low_level_spec: (unit -> (KSt -> Prop))) ,
  (“ (csr_wf1 g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_l_low_level_spec fin_l_low_level_spec ) ” 
  &&  “ ((adj_verts (g_low_level_spec)) = n_pre) ” 
  &&  “ (safeExec (pre_dfs1 (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (vis1_l_low_level_spec) (fin_l_low_level_spec) (timer_v_low_level_spec)) (dfs_finish (g_low_level_spec) (u_pre)) X_low_level_spec ) ” 
  &&  “ (0 <= u_pre) ” 
  &&  “ (u_pre < n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ ((Znth (u_pre) (vis1_l_low_level_spec) (0)) = 0) ” 
  &&  “ (0 <= timer_v_low_level_spec) ” 
  &&  “ (timer_v_low_level_spec <= (count_nonzero (vis1_l_low_level_spec))) ”
  &&  (IntArray.full radj_col_pre (m_of (radj_row_l_low_level_spec)) radj_col_l_low_level_spec )
  **  (IntArray.full radj_row_pre (n_pre + 1 ) radj_row_l_low_level_spec )
  **  (IntArray.full vis1_pre n_pre vis1_l_low_level_spec )
  **  (IntArray.full fin_pre n_pre fin_l_low_level_spec )
  **  (IntArray.full timer_p_pre 1 (cons (timer_v_low_level_spec) (nil)) ))
  **
  ((EX timer_v__2 vis1_l__2 fin_l__2,
  “ (csr_wf1 g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec vis1_l__2 fin_l__2 ) ” 
  &&  “ ((adj_verts (g_low_level_spec)) = n_pre) ” 
  &&  “ (safeExec (pre_dfs1 (g_low_level_spec) (radj_col_l_low_level_spec) (radj_row_l_low_level_spec) (vis1_l__2) (fin_l__2) (timer_v__2)) (return (tt)) X_low_level_spec ) ” 
  &&  “ (0 <= timer_v__2) ” 
  &&  “ (((count_nonzero (vis1_l__2)) - timer_v__2 ) = ((count_nonzero (vis1_l_low_level_spec)) - timer_v_low_level_spec )) ”
  &&  (IntArray.full radj_col_pre (m_of (radj_row_l_low_level_spec)) radj_col_l_low_level_spec )
  **  (IntArray.full radj_row_pre (n_pre + 1 ) radj_row_l_low_level_spec )
  **  (IntArray.full vis1_pre n_pre vis1_l__2 )
  **  (IntArray.full fin_pre n_pre fin_l__2 )
  **  (IntArray.full timer_p_pre 1 (cons (timer_v__2) (nil)) ))
  -*
  (EX timer_v_ vis1_l_ fin_l_,
  “ (csr_wf1 g_bind_spec radj_col_l_bind_spec radj_row_l_bind_spec vis1_l_ fin_l_ ) ” 
  &&  “ ((adj_verts (g_bind_spec)) = n_pre) ” 
  &&  “ (safeExec (pre_dfs1 (g_bind_spec) (radj_col_l_bind_spec) (radj_row_l_bind_spec) (vis1_l_) (fin_l_) (timer_v_)) (applyf (f_bind_spec) (tt)) X_bind_spec ) ” 
  &&  “ (0 <= timer_v_) ” 
  &&  “ (((count_nonzero (vis1_l_)) - timer_v_ ) = ((count_nonzero (vis1_l_bind_spec)) - timer_v_bind_spec )) ”
  &&  (IntArray.full radj_col_pre (m_of (radj_row_l_bind_spec)) radj_col_l_bind_spec )
  **  (IntArray.full radj_row_pre (n_pre + 1 ) radj_row_l_bind_spec )
  **  (IntArray.full vis1_pre n_pre vis1_l_ )
  **  (IntArray.full fin_pre n_pre fin_l_ )
  **  (IntArray.full timer_p_pre 1 (cons (timer_v_) (nil)) )))
.

Module Type VC_Correct.

Include safeexecE_Strategy_Correct.
Include int_array_Strategy_Correct.
Include uint_array_Strategy_Correct.
Include undef_uint_array_Strategy_Correct.
Include array_shape_Strategy_Correct.

Axiom proof_of_dfs1_safety_wit_1 : dfs1_safety_wit_1.
Axiom proof_of_dfs1_safety_wit_2 : dfs1_safety_wit_2.
Axiom proof_of_dfs1_safety_wit_3 : dfs1_safety_wit_3.
Axiom proof_of_dfs1_safety_wit_4 : dfs1_safety_wit_4.
Axiom proof_of_dfs1_safety_wit_5 : dfs1_safety_wit_5.
Axiom proof_of_dfs1_safety_wit_6 : dfs1_safety_wit_6.
Axiom proof_of_dfs1_safety_wit_7 : dfs1_safety_wit_7.
Axiom proof_of_dfs1_safety_wit_8 : dfs1_safety_wit_8.
Axiom proof_of_dfs1_safety_wit_9 : dfs1_safety_wit_9.
Axiom proof_of_dfs1_safety_wit_10 : dfs1_safety_wit_10.
Axiom proof_of_dfs1_safety_wit_11 : dfs1_safety_wit_11.
Axiom proof_of_dfs1_safety_wit_12 : dfs1_safety_wit_12.
Axiom proof_of_dfs1_entail_wit_1 : dfs1_entail_wit_1.
Axiom proof_of_dfs1_entail_wit_2 : dfs1_entail_wit_2.
Axiom proof_of_dfs1_entail_wit_3_1 : dfs1_entail_wit_3_1.
Axiom proof_of_dfs1_entail_wit_3_2 : dfs1_entail_wit_3_2.
Axiom proof_of_dfs1_return_wit_1 : dfs1_return_wit_1.
Axiom proof_of_dfs1_partial_solve_wit_1 : dfs1_partial_solve_wit_1.
Axiom proof_of_dfs1_partial_solve_wit_2 : dfs1_partial_solve_wit_2.
Axiom proof_of_dfs1_partial_solve_wit_3 : dfs1_partial_solve_wit_3.
Axiom proof_of_dfs1_partial_solve_wit_4 : dfs1_partial_solve_wit_4.
Axiom proof_of_dfs1_partial_solve_wit_5 : dfs1_partial_solve_wit_5.
Axiom proof_of_dfs1_partial_solve_wit_6_pure : dfs1_partial_solve_wit_6_pure.
Axiom proof_of_dfs1_partial_solve_wit_6 : dfs1_partial_solve_wit_6.
Axiom proof_of_dfs1_partial_solve_wit_7 : dfs1_partial_solve_wit_7.
Axiom proof_of_dfs1_partial_solve_wit_8 : dfs1_partial_solve_wit_8.
Axiom proof_of_dfs1_partial_solve_wit_9 : dfs1_partial_solve_wit_9.
Axiom proof_of_dfs2_safety_wit_1 : dfs2_safety_wit_1.
Axiom proof_of_dfs2_safety_wit_2 : dfs2_safety_wit_2.
Axiom proof_of_dfs2_safety_wit_3 : dfs2_safety_wit_3.
Axiom proof_of_dfs2_safety_wit_4 : dfs2_safety_wit_4.
Axiom proof_of_dfs2_safety_wit_5 : dfs2_safety_wit_5.
Axiom proof_of_dfs2_safety_wit_6 : dfs2_safety_wit_6.
Axiom proof_of_dfs2_safety_wit_7 : dfs2_safety_wit_7.
Axiom proof_of_dfs2_safety_wit_8 : dfs2_safety_wit_8.
Axiom proof_of_dfs2_entail_wit_1 : dfs2_entail_wit_1.
Axiom proof_of_dfs2_entail_wit_2 : dfs2_entail_wit_2.
Axiom proof_of_dfs2_entail_wit_3_1 : dfs2_entail_wit_3_1.
Axiom proof_of_dfs2_entail_wit_3_2 : dfs2_entail_wit_3_2.
Axiom proof_of_dfs2_return_wit_1 : dfs2_return_wit_1.
Axiom proof_of_dfs2_partial_solve_wit_1 : dfs2_partial_solve_wit_1.
Axiom proof_of_dfs2_partial_solve_wit_2 : dfs2_partial_solve_wit_2.
Axiom proof_of_dfs2_partial_solve_wit_3 : dfs2_partial_solve_wit_3.
Axiom proof_of_dfs2_partial_solve_wit_4 : dfs2_partial_solve_wit_4.
Axiom proof_of_dfs2_partial_solve_wit_5 : dfs2_partial_solve_wit_5.
Axiom proof_of_dfs2_partial_solve_wit_6 : dfs2_partial_solve_wit_6.
Axiom proof_of_dfs2_partial_solve_wit_7 : dfs2_partial_solve_wit_7.
Axiom proof_of_dfs2_partial_solve_wit_8_pure : dfs2_partial_solve_wit_8_pure.
Axiom proof_of_dfs2_partial_solve_wit_8 : dfs2_partial_solve_wit_8.
Axiom proof_of_dfs2_derive_bind_spec_by_low_level_spec : dfs2_derive_bind_spec_by_low_level_spec.
Axiom proof_of_dfs1_derive_bind_spec_by_low_level_spec : dfs1_derive_bind_spec_by_low_level_spec.

End VC_Correct.
