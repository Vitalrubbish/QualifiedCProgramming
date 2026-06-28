Require Import Coq.Classes.EquivDec.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Lists.List.
Require Import SetsClass.SetsClass.
From MonadLib.StateRelMonad Require Import StateRelBasic StateRelHoare FixpointLib.
From GraphLib Require Import graph_basic Syntax.
From GraphLib.examples Require Import tarjan.
From MaxMinLib Require Import MaxMin Interface.
From Algorithms.Tarjan_directed Require Import
  SCC_basic Tarjan_scc Tarjan_scc_basics Tarjan_scc_is_dfn
  Tarjan_scc_low_defs Tarjan_scc_low_pure.

Import SetsNotation.
Import MonadNotation.
Local Open Scope sets.
Local Open Scope monad.

Section LOW_PRIMITIVES.

  Context {V E: Type}
          `{EqDec V eq}
          (g: OriginalGraphType V E)
          `{OriginalGraph_gvalid g}
          (root: V)
          (g_vvalid_root: original_vvalid g root).

  (* ================================================================ *)
  (* Preloop entry facts                                             *)
  (* ================================================================ *)

  Lemma preloop_low_eq_dfn (u: V):
    Hoare (fun s: @SCCSt V => True)
          (preloop u)
          (fun _ s => low s u = dfn s u).
  Proof.
    unfold preloop. unfold_op. intro_state. hoare_auto_s.
    subst s. simpl.
    unfold equiv_decb. destruct (equiv_dec u u) as [Heq | Hneq];
      [reflexivity | exfalso; apply Hneq; reflexivity].
  Qed.

  Lemma preloop_establishes_low_iteration_entry (u: V):
    Hoare (fun s: @SCCSt V =>
             low_pre g root u s /\ stack_dfn_order s /\ dfn_injective s)
          (preloop u)
          (fun _ s => low_iteration_entry g root u s).
  Proof.
    unfold low_pre, low_iteration_entry.
    apply Hoare_conj with
      (Q1 := fun _ s => low_iteration_inv g root u ∅ s)
      (Q2 := fun _ s => stack_dfn_order s /\ dfn_injective s).
    - (* Part 1: low_iteration_inv g root u ∅ *)
      unfold low_iteration_inv.
      apply Hoare_conj with
        (Q1 := fun _ s => wf_scc_state g root s)
        (Q2 := fun _ s => u ∈ visited s /\ In u (stack s) /\
                          done_visited ∅ s /\ low_frontier g u ∅ s /\
                          low_src g u ∅ s /\
                          children_low_valid g root u ∅ s /\
                          fa_child_of_u g u s /\
                          fa_not_done_implies_eq_u u ∅ s).
      + (* wf_scc_state *)
        eapply Hoare_conseq_pre.
        2: apply (preloop_preserves_wf_scc_state g root u).
        unfold wf_scc_state_pre. intros s. tauto.
      + (* Remaining 8 conjuncts *)
        apply Hoare_conj with
          (Q1 := fun _ s => u ∈ visited s)
          (Q2 := fun _ s => In u (stack s) /\ done_visited ∅ s /\
                            low_frontier g u ∅ s /\ low_src g u ∅ s /\
                            children_low_valid g root u ∅ s /\
                            fa_child_of_u g u s /\
                            fa_not_done_implies_eq_u u ∅ s).
        * (* u ∈ visited *)
          eapply Hoare_conseq_pre.
          2: apply (preloop_self_visited u).
          intros s. tauto.
        * (* Remaining 7 conjuncts *)
          apply Hoare_conj with
            (Q1 := fun _ s => In u (stack s))
            (Q2 := fun _ s => done_visited ∅ s /\ low_frontier g u ∅ s /\
                              low_src g u ∅ s /\
                              children_low_valid g root u ∅ s /\
                              fa_child_of_u g u s /\
                              fa_not_done_implies_eq_u u ∅ s).
          -- (* In u (stack s) *)
            eapply Hoare_conseq_pre.
            2: apply (preloop_in_stack u).
            intros s. tauto.
          -- (* Remaining 6 conjuncts — prove directly via intro_state *)
            unfold preloop. unfold_op. intro_state. hoare_auto_s.
            subst s. simpl.
            destruct H as [Hpre [Horder Hinj]].
            destruct Hpre as [Hwf Hnuvis].
            unfold wf_scc_state in Hwf.
            destruct Hwf as [_ [_ [_ Hfa]]].
            split; [| split; [| split; [| split; [| split; [| ]]]]].
            ++ (* done_visited ∅ *)
              unfold done_visited. intros w Hempty. destruct Hempty.
            ++ (* low_frontier g u ∅ *)
              unfold low_frontier.
              split; [| intros v Hempty; destruct Hempty].
              simpl. unfold equiv_decb.
              destruct (equiv_dec u u) as [Heq | Hneq];
                [apply le_n | exfalso; apply Hneq; reflexivity].
            ++ (* low_src g u ∅ *)
              unfold low_src. left. simpl.
              unfold equiv_decb.
              destruct (equiv_dec u u) as [Heq | Hneq];
                [reflexivity | exfalso; apply Hneq; reflexivity].
            ++ (* children_low_valid g root u ∅ *)
              unfold children_low_valid.
              intros v Hempty. destruct Hempty.
            ++ (* fa_child_of_u g u *)
              unfold fa_child_of_u.
              intros v [Hfa_v Hfa_neq].
              simpl in Hfa_v, Hfa_neq.
              apply Hfa in Hfa_neq.
              rewrite Hfa_v in Hfa_neq.
              exfalso. apply Hnuvis. exact Hfa_neq.
            ++ (* fa_not_done_implies_eq_u u ∅ *)
              unfold fa_not_done_implies_eq_u.
              intros v _ Hfa_v.
              simpl in Hfa_v.
              destruct (equiv_dec v u) as [Heq | Hneq]; [exact Heq | exfalso].
              assert (Hfa_neq: fa s0 v <> v). {
                intro Heq_fa. apply Hneq. rewrite <- Heq_fa. exact Hfa_v.
              }
              apply Hfa in Hfa_neq.
              rewrite Hfa_v in Hfa_neq.
              apply Hnuvis. exact Hfa_neq.
    - (* Part 2: stack_dfn_order /\ dfn_injective *)
      apply Hoare_conj.
      + (* stack_dfn_order *)
        eapply Hoare_conseq_pre.
        2: apply (preloop_preserves_stack_dfn_order u).
        intros s Hpre.
        destruct Hpre as [[Hwf Hnuvis] [Horder Hinj]].
        unfold wf_scc_state in Hwf.
        destruct Hwf as [Hsiv [Hinv _]].
        split; [exact Horder | split; [exact Hinv | split; [exact Hsiv | exact Hnuvis]]].
      + (* dfn_injective *)
        eapply Hoare_conseq_pre.
        2: apply (preloop_preserves_dfn_injective u).
        intros s Hpre.
        destruct Hpre as [[Hwf Hnuvis] [Horder Hinj]].
        unfold wf_scc_state in Hwf.
        destruct Hwf as [_ [Hinv _]].
        split; [exact Hinj | split; [exact Hinv | exact Hnuvis]].
  Qed.

  (* ================================================================ *)
  (* Low-update preservation contracts                               *)
  (* ================================================================ *)

  Lemma update_low_preserves_done_visited (u: V) (done: V -> Prop) (n: nat):
    Hoare (fun s: @SCCSt V => done_visited done s)
          (update_low u n)
          (fun _ s => done_visited done s).
  Proof.
    unfold done_visited. apply (update_low_keep_visited_forall u n done).
  Qed.

  Lemma update_low_other_preserves_low_iteration_frame
        (u a: V) (done: V -> Prop) (n: nat):
    a <> u ->
    ~ done a ->
    Hoare (fun s: @SCCSt V => low_iteration_inv g root u done s)
          (update_low a n)
          (fun _ s =>
             wf_scc_state g root s /\
             u ∈ visited s /\
             In u (stack s) /\
             done_visited done s /\
             low_frontier g u done s /\
             low_src g u done s /\
             fa_child_of_u g u s /\
             fa_not_done_implies_eq_u u done s).
  Proof.
    intros Hneq Hndone.
    unfold update_low. unfold_op. intro_state. hoare_auto_s.
    { (* Branch: n < low s0 a, set_low a n executed *)
      subst s. unfold RecordSet.set. simpl.
      destruct H as (Hwf & Huvis & Hustack & Hdonevis & Hfront & Hsrc & Hchild & Hfa_child & Hfa_not).
      split; [| split; [| split; [| split; [| split; [| split; [| split; [| ]]]]]]].
      - (* wf_scc_state *)
        unfold wf_scc_state in Hwf |- *.
        destruct Hwf as [Hsiv [Hinv [Hvalid Hfa_vis]]].
        split; [exact Hsiv | split; [exact Hinv | split; [exact Hvalid | exact Hfa_vis]]].
      - (* u ∈ visited *) exact Huvis.
      - (* In u (stack s) *) exact Hustack.
      - (* done_visited *) exact Hdonevis.
      - (* low_frontier *)
        unfold low_frontier in Hfront |- *.
        destruct Hfront as [Hle Hrest].
        split.
        { simpl. unfold equiv_decb.
          destruct (equiv_dec u a) as [Heq | Hneq'].
          { exfalso. apply Hneq. symmetry. exact Heq. }
          { exact Hle. } }
        { simpl. intros v Hdone_v Hdg.
          specialize (Hrest v Hdone_v Hdg).
          destruct Hrest as [Hfa_part Hstack_part].
          split.
          - unfold equiv_decb.
            destruct (equiv_dec u a) as [Heq_ua | Hneq_ua].
            { exfalso. apply Hneq. symmetry. exact Heq_ua. }
            { destruct (equiv_dec v a) as [Heq_va | Hneq_va].
              { exfalso. apply Hndone. rewrite <- Heq_va. exact Hdone_v. }
              { intro Hfa_v. apply Hfa_part. exact Hfa_v. } }
          - unfold equiv_decb.
            destruct (equiv_dec u a) as [Heq_ua | Hneq_ua].
            { exfalso. apply Hneq. symmetry. exact Heq_ua. }
            { intro Hstk_v. apply Hstack_part. exact Hstk_v. } }
      - (* low_src *)
        unfold low_src in Hsrc |- *.
        destruct Hsrc as [Hlow_eq | [(v & Hdone_v & Hdg & Hfa_eq & Hfa_neq & Hlow_eq) |
                                    (w & Hdone_w & Hdg_w & Hstk_w & Hfa_neq_w & Hlow_eq_w)]].
        { left. simpl. unfold equiv_decb.
          destruct (equiv_dec u a) as [Heq | Hneq'].
          { exfalso. apply Hneq. symmetry. exact Heq. }
          { exact Hlow_eq. } }
        { right. left. exists v.
          split; [exact Hdone_v | split; [exact Hdg | split; [exact Hfa_eq |
            split; [exact Hfa_neq |]]]].
          simpl. unfold equiv_decb.
          destruct (equiv_dec u a) as [Heq_ua | Hneq_ua].
          { exfalso. apply Hneq. symmetry. exact Heq_ua. }
          { destruct (equiv_dec v a) as [Heq_va | Hneq_va].
            { exfalso. apply Hndone. rewrite <- Heq_va. exact Hdone_v. }
            { exact Hlow_eq. } } }
        { right. right. exists w.
          split; [exact Hdone_w | split; [exact Hdg_w | split; [exact Hstk_w |
            split; [exact Hfa_neq_w |]]]].
          simpl. unfold equiv_decb.
          destruct (equiv_dec u a) as [Heq_ua | Hneq_ua].
          { exfalso. apply Hneq. symmetry. exact Heq_ua. }
          { exact Hlow_eq_w. } }
      - (* fa_child_of_u *) exact Hfa_child.
      - (* fa_not_done_implies_eq_u *) exact Hfa_not. }
    { (* Branch: ~ n < low s0 a, skip *)
      destruct H1 as [Heq _]. subst s.
      destruct H as (Hwf & Huvis & Hustack & Hdonevis & Hfront & Hsrc & Hchild & Hfa_child & Hfa_not).
      split; [exact Hwf | split; [exact Huvis | split; [exact Hustack |
        split; [exact Hdonevis | split; [exact Hfront | split; [exact Hsrc |
          split; [exact Hfa_child | exact Hfa_not]]]]]]]. }
  Qed.

  Lemma set_low_preserves_scc_low_valid_v_when_not_child
        (v a: V) (n: nat) (s: @SCCSt V):
    v <> a ->
    ~ dg_step (state_to_dfs_tree g s root) v a ->
    scc_low_valid_v g root s v ->
    scc_low_valid_v g root
      (RecordSet.set low (fun low0 x => if equiv_decb x a then n else low0 x) s) v.
  Proof.
    intros Hneq_va Hnot_child Hvalid.
    unfold scc_low_valid_v, min_value_of_subset, min_object_of_subset in *.
    destruct Hvalid as [m [[Hm_src Hm_min] Hm_eq]].
    exists m. split.
    - split.
      + destruct Hm_src as [Hm_child | Hm_back].
        * left. destruct Hm_child as [x [[Htree_x Hmin_x] Hx_eq]].
          exists x. split.
          -- split.
             ++ simpl. exact Htree_x.
             ++ intros y Htree_y. simpl in Htree_y |- *.
                assert (Hx_ne_a: x <> a).
                { intro Hxa. subst x. apply Hnot_child. exact Htree_x. }
                assert (Hy_ne_a: y <> a).
                { intro Hya. subst y. apply Hnot_child. exact Htree_y. }
                simpl. unfold equiv_decb.
                destruct (equiv_dec x a) as [Heq_xa | Hneq_xa];
                  [exfalso; apply Hx_ne_a; exact Heq_xa |].
                destruct (equiv_dec y a) as [Heq_ya | Hneq_ya];
                  [exfalso; apply Hy_ne_a; exact Heq_ya |].
                apply Hmin_x. exact Htree_y.
          -- simpl. unfold equiv_decb.
             destruct (equiv_dec x a) as [Heq_xa | Hneq_xa].
             ++ exfalso. apply Hnot_child. rewrite Heq_xa in Htree_x. exact Htree_x.
             ++ exact Hx_eq.
        * right. destruct Hm_back as [x [[Hx Hmin_x] Hx_eq]].
          exists x. split.
          -- split.
             ++ simpl. exact Hx.
             ++ intros y Hy. simpl in Hy |- *. apply Hmin_x. exact Hy.
          -- simpl. exact Hx_eq.
      + intros k Hk.
        apply Hm_min.
        destruct Hk as [Hk_child | Hk_back].
        * left. destruct Hk_child as [x [[Htree_x Hmin_x] Hx_eq]].
          exists x. split.
          -- split.
             ++ simpl in Htree_x. exact Htree_x.
             ++ intros y Htree_y.
                simpl in Htree_y.
                specialize (Hmin_x y Htree_y).
                simpl in Hmin_x.
                assert (Hx_ne_a: x <> a).
                { intro Hxa. subst x. apply Hnot_child. exact Htree_x. }
                assert (Hy_ne_a: y <> a).
                { intro Hya. subst y. apply Hnot_child. exact Htree_y. }
                unfold equiv_decb in Hmin_x.
                destruct (equiv_dec x a) as [Heq_xa | Hneq_xa];
                  [exfalso; apply Hx_ne_a; exact Heq_xa |].
                destruct (equiv_dec y a) as [Heq_ya | Hneq_ya];
                  [exfalso; apply Hy_ne_a; exact Heq_ya |].
                exact Hmin_x.
          -- simpl in Hx_eq. unfold equiv_decb in Hx_eq.
             destruct (equiv_dec x a) as [Heq_xa | Hneq_xa].
             ++ exfalso. apply Hnot_child. rewrite Heq_xa in Htree_x. exact Htree_x.
             ++ exact Hx_eq.
        * right. destruct Hk_back as [x [[Hx Hmin_x] Hx_eq]].
          exists x. split.
          -- split.
             ++ simpl in Hx. exact Hx.
             ++ intros y Hy. simpl in Hy. apply Hmin_x. exact Hy.
          -- simpl in Hx_eq. exact Hx_eq.
    - simpl. unfold equiv_decb.
      destruct (equiv_dec v a) as [Heq_va | Hneq_va'].
      + exfalso. apply Hneq_va. exact Heq_va.
      + exact Hm_eq.
  Qed.

  Lemma update_low_preserves_children_low_valid_when_not_tree_child
        (u a: V) (done: V -> Prop) (n: nat):
    ~ done a ->
    Hoare (fun s: @SCCSt V =>
             children_low_valid g root u done s /\
             (forall v,
                done v ->
                dg_step g u v ->
                fa s v = u ->
                fa s v <> v ->
                ~ dg_step (state_to_dfs_tree g s root) v a))
          (update_low a n)
          (fun _ s => children_low_valid g root u done s).
  Proof.
    intros Hndone.
    unfold update_low. unfold_op. intro_state. hoare_auto_s.
    { (* Branch: n < low s0 a, set_low a n executed *)
      subst s. unfold RecordSet.set. simpl.
      destruct H as [Hchild Hnot_child].
      unfold children_low_valid in Hchild |- *.
      intros v Hdone_v Hdg_v Hfa_eq Hfa_neq_v.
      simpl in Hfa_eq, Hfa_neq_v.
      apply (set_low_preserves_scc_low_valid_v_when_not_child v a n s0).
      - intro Heq_va. subst v. apply Hndone. exact Hdone_v.
      - apply Hnot_child; auto.
      - apply Hchild; auto. }
    { (* Branch: ~ n < low s0 a, skip *)
      destruct H1 as [Heq _]. subst s. destruct H. assumption. }
  Qed.

  Lemma update_low_other_preserves_low_iteration_inv_when_not_child
        (u a: V) (done: V -> Prop) (n: nat):
    a <> u ->
    ~ done a ->
    Hoare (fun s: @SCCSt V =>
             low_iteration_inv g root u done s /\
             (forall v,
                done v ->
                dg_step g u v ->
                fa s v = u ->
                fa s v <> v ->
                ~ dg_step (state_to_dfs_tree g s root) v a))
          (update_low a n)
          (fun _ s => low_iteration_inv g root u done s).
  Proof.
    intros Hneq Hndone.
    eapply Hoare_conseq_post.
    2: {
      apply Hoare_conj with
        (Q1 := fun _ s =>
          wf_scc_state g root s /\
          u ∈ visited s /\
          In u (stack s) /\
          done_visited done s /\
          low_frontier g u done s /\
          low_src g u done s /\
          fa_child_of_u g u s /\
          fa_not_done_implies_eq_u u done s)
        (Q2 := fun _ s => children_low_valid g root u done s).
      - eapply Hoare_conseq_pre.
        2: apply (update_low_other_preserves_low_iteration_frame u a done n Hneq Hndone).
        intros s [Hiter _]. exact Hiter.
      - eapply Hoare_conseq_pre.
        2: apply (update_low_preserves_children_low_valid_when_not_tree_child u a done n Hndone).
        intros s Hpre.
        destruct Hpre as [Hiter Hnot_child].
        destruct Hiter as (Hwf & Huvis & Hustack & Hdonevis & Hfront & Hsrc & Hchild & Hfa_child & Hfa_not).
        split; [exact Hchild | exact Hnot_child]. }
    intros _ s [Hframe Hchild].
    destruct Hframe as (Hwf & Huvis & Hustack & Hdonevis & Hfront & Hsrc & Hfa_child & Hfa_not).
    unfold low_iteration_inv.
    split; [exact Hwf | split; [exact Huvis | split; [exact Hustack |
      split; [exact Hdonevis | split; [exact Hfront | split; [exact Hsrc |
        split; [exact Hchild | split; [exact Hfa_child | exact Hfa_not]]]]]]]].
  Qed.

  (* ================================================================ *)
  (* Tree-edge setup contracts                                       *)
  (* ================================================================ *)

  Lemma set_fa_unvisited_preserves_tree_step
        (a p x y: V) (s: @SCCSt V):
    ~ a ∈ visited s ->
    (dg_step (state_to_dfs_tree g
       (RecordSet.set fa (fun fa0 z => if equiv_decb z a then p else fa0 z) s) root) x y <->
     dg_step (state_to_dfs_tree g s root) x y).
  Proof.
    intros Hnv. split.
    - (* -> direction *)
      unfold dg_step. intros [e [Hstep_orig [Hfst Hsnd]]].
      exists e. split; [| split; [exact Hfst | exact Hsnd]].
      unfold state_to_dfs_tree in Hstep_orig |- *; simpl in Hstep_orig |- *.
      unfold original_step in Hstep_orig |- *; simpl in Hstep_orig |- *.
      destruct Hstep_orig as [v [Hv_vis [Hfa_neq [Hfst_eq Hsnd_eq]]]].
      simpl in Hfa_neq, Hfst_eq. unfold equiv_decb in Hfa_neq, Hfst_eq.
      destruct (equiv_dec v a) as [Heq | Hneq'].
      { exfalso. apply Hnv. rewrite <- Heq. exact Hv_vis. }
      { exists v. split; [exact Hv_vis | split; [exact Hfa_neq | split; [exact Hfst_eq | exact Hsnd_eq]]]. }
    - (* <- direction *)
      unfold dg_step. intros [e [Hstep_orig [Hfst Hsnd]]].
      exists e. split; [| split; [exact Hfst | exact Hsnd]].
      unfold state_to_dfs_tree in Hstep_orig |- *; simpl in Hstep_orig |- *.
      unfold original_step in Hstep_orig |- *; simpl in Hstep_orig |- *.
      destruct Hstep_orig as [v [Hv_vis [Hfa_neq [Hfst_eq Hsnd_eq]]]].
      destruct (equiv_decb v a) eqn:Heq_decb.
      { (* v ==b a = true, so v = a *) exfalso.
        unfold equiv_decb in Heq_decb.
        destruct (equiv_dec v a) as [Heq_va | Hneq_va]; [| discriminate Heq_decb].
        apply Hnv. rewrite <- Heq_va. exact Hv_vis. }
      { (* v ==b a = false, so v <> a *)
        exists v. rewrite Heq_decb. simpl.
        split; [exact Hv_vis | split; [exact Hfa_neq | split; [exact Hfst_eq | exact Hsnd_eq]]]. }
  Qed.

  Lemma set_fa_preserves_scc_low_valid_v_when_unvisited
        (v a p: V) (s: @SCCSt V):
    ~ a ∈ visited s ->
    scc_low_valid_v g root s v ->
    scc_low_valid_v g root
      (RecordSet.set fa (fun fa0 x => if equiv_decb x a then p else fa0 x) s) v.
  Proof.
    intros Hnv Hvalid.
    unfold scc_low_valid_v, min_value_of_subset, min_object_of_subset in *.
    destruct Hvalid as [m [[Hm_src Hm_min] Hm_eq]].
    exists m. split; [| simpl; exact Hm_eq].
    split.
    - destruct Hm_src as [Hm_child | Hm_back].
      + left. destruct Hm_child as [x [[Htree_x Hmin_x] Hx_eq]].
        exists x. split; [| simpl; exact Hx_eq].
        split.
        * apply (proj2 (set_fa_unvisited_preserves_tree_step a p v x s Hnv)).
          exact Htree_x.
        * intros y Htree_y.
          simpl.
          apply Hmin_x.
          apply (proj1 (set_fa_unvisited_preserves_tree_step a p v y s Hnv)).
          exact Htree_y.
      + right. destruct Hm_back as [x [[Hx Hmin_x] Hx_eq]].
        exists x. split; [| simpl; exact Hx_eq].
        split.
        * sets_unfold in Hx. sets_unfold.
          destruct Hx as [Hback | Heq_x].
          -- left. unfold scc_back_edge in Hback |- *.
             destruct Hback as [Hdg_x [Hstk_x Hnot_tree_x]].
             split; [exact Hdg_x | split; [exact Hstk_x |]].
             intro Htree_new. apply Hnot_tree_x.
             apply (proj1 (set_fa_unvisited_preserves_tree_step a p v x s Hnv)).
             exact Htree_new.
          -- right. exact Heq_x.
        * intros y Hy.
          simpl.
          apply Hmin_x.
          sets_unfold in Hy. sets_unfold.
          destruct Hy as [Hback | Heq_y].
          -- left. unfold scc_back_edge in Hback |- *.
             destruct Hback as [Hdg_y [Hstk_y Hnot_tree_y]].
             split; [exact Hdg_y | split; [exact Hstk_y |]].
             intro Htree_old. apply Hnot_tree_y.
             apply (proj2 (set_fa_unvisited_preserves_tree_step a p v y s Hnv)).
             exact Htree_old.
          -- right. exact Heq_y.
    - intros n Hn.
      apply Hm_min.
      destruct Hn as [Hn_child | Hn_back].
      + left. destruct Hn_child as [x [[Htree_x Hmin_x] Hx_eq]].
        exists x. split; [| simpl in Hx_eq; exact Hx_eq].
        split.
        * apply (proj1 (set_fa_unvisited_preserves_tree_step a p v x s Hnv)).
          exact Htree_x.
        * intros y Htree_y.
          specialize (Hmin_x y).
          simpl in Hmin_x.
          apply Hmin_x.
          apply (proj2 (set_fa_unvisited_preserves_tree_step a p v y s Hnv)).
          exact Htree_y.
      + right. destruct Hn_back as [x [[Hx Hmin_x] Hx_eq]].
        exists x. split; [| simpl in Hx_eq; exact Hx_eq].
        split.
        * sets_unfold in Hx. sets_unfold.
          destruct Hx as [Hback | Heq_x].
          -- left. unfold scc_back_edge in Hback |- *.
             destruct Hback as [Hdg_x [Hstk_x Hnot_tree_x]].
             split; [exact Hdg_x | split; [exact Hstk_x |]].
             intro Htree_old. apply Hnot_tree_x.
             apply (proj2 (set_fa_unvisited_preserves_tree_step a p v x s Hnv)).
             exact Htree_old.
          -- right. exact Heq_x.
        * intros y Hy.
          simpl in Hmin_x.
          apply Hmin_x.
          sets_unfold in Hy. sets_unfold.
          destruct Hy as [Hback | Heq_y].
          -- left. unfold scc_back_edge in Hback |- *.
             destruct Hback as [Hdg_y [Hstk_y Hnot_tree_y]].
             split; [exact Hdg_y | split; [exact Hstk_y |]].
             intro Htree_new. apply Hnot_tree_y.
             apply (proj1 (set_fa_unvisited_preserves_tree_step a p v y s Hnv)).
             exact Htree_new.
          -- right. exact Heq_y.
  Qed.

  Lemma set_fa_establishes_new_child_parent
        (u a: V):
    Hoare (fun s: @SCCSt V =>
             dg_step g u a /\
             u ∈ visited s /\
             ~ a ∈ visited s)
          (set_fa a u)
          (fun _ s =>
             fa s a = u /\
             fa s a <> a).
  Proof.
    unfold set_fa. intro_state. hoare_auto_s.
    subst s. simpl. unfold equiv_decb.
    destruct H as [_ [Huvis Havis]].
    destruct (equiv_dec a a) as [_ | Hc]; [| exfalso; apply Hc; reflexivity].
    split; [reflexivity |].
    intro Hua. apply Havis. rewrite <- Hua. exact Huvis.
  Qed.

  Lemma set_fa_visit_establishes_new_child_tree_edge
        (u a: V):
    Hoare (fun s: @SCCSt V =>
             dg_step g u a /\
             u ∈ visited s /\
             ~ a ∈ visited s)
          (set_fa a u;; visit a)
          (fun _ s =>
             fa s a = u /\
             fa s a <> a /\
             dg_step (state_to_dfs_tree g s root) u a).
  Proof.
    unfold set_fa, visit. unfold_op. intro_state. hoare_auto_s.
    subst s. unfold RecordSet.set. simpl.
    destruct H as (Hdg & Hu_vis & Ha_nvis).
    split.
    - (* fa a = u *) simpl. unfold equiv_decb.
      destruct (equiv_dec a a) as [_ | Hc]; [reflexivity | exfalso; apply Hc; reflexivity].
    - split.
      + (* fa a <> a *) simpl. unfold equiv_decb.
        destruct (equiv_dec a a) as [_ | Hc]; [| exfalso; apply Hc; reflexivity].
        intro Heq. apply Ha_nvis. rewrite <- Heq. exact Hu_vis.
      + (* dg_step (state_to_dfs_tree ...) u a *)
        unfold state_to_dfs_tree. simpl.
        destruct Hdg as [e [Horig_step [Hfst_eq Hsnd_eq]]].
        unfold dg_step.
        exists e. split.
        { unfold original_step. simpl.
          exists a. split.
          - sets_unfold. right. reflexivity.
          - split.
            * unfold equiv_decb. destruct (equiv_dec a a) as [_ | Hc]; [| exfalso; apply Hc; reflexivity].
              intro Heq. apply Ha_nvis. rewrite <- Heq. exact Hu_vis.
            * split.
              -- unfold equiv_decb. destruct (equiv_dec a a) as [_ | Hc]; [| exfalso; apply Hc; reflexivity].
                 rewrite Hfst_eq. reflexivity.
              -- exact Hsnd_eq. }
        { split; [exact Hfst_eq | exact Hsnd_eq]. }
  Qed.

  Lemma set_fa_establishes_low_iteration_before_new_child
        (u a: V) (done: V -> Prop):
    Hoare (fun s: @SCCSt V =>
             low_iteration_inv g root u done s /\
             ~ a ∈ visited s /\
             ~ done a /\
             dg_step g u a)
          (set_fa a u)
          (fun _ s =>
             wf_scc_state_pre g root a s /\
             u ∈ visited s /\
             In u (stack s) /\
             done_visited done s /\
             low_frontier g u done s /\
             low_src g u done s /\
             children_low_valid g root u done s /\
             fa_child_of_u g u s /\
             fa s a = u).
  Proof.
    unfold set_fa. intro_state. hoare_auto_s.
    subst s. unfold RecordSet.set. simpl.
    destruct H as (Hinv & Hnv & Hndone & Hdg).
    destruct Hinv as (Hwf & Huvis & Hustack & Hdonevis & Hfront & Hsrc & Hchild & Hfa_child & Hfa_not).
    split; [| split; [| split; [| split; [| split; [| split; [| split; [| split; [| ]]]]]]]].
    - (* wf_scc_state_pre g root a *)
      unfold wf_scc_state_pre. split.
      + (* wf_scc_state *)
        unfold wf_scc_state in Hwf |- *.
        destruct Hwf as [Hsiv [Hinv_dfn [Hvalid Hfa_vis]]].
        split; [exact Hsiv | split; [exact Hinv_dfn | split; [|]]].
        * (* dfn_valid: state_to_dfs_tree unchanged because a ∉ visited *)
          unfold dfn_valid in Hvalid |- *.
          intros x y Hstep.
          apply Hvalid.
          unfold state_to_dfs_tree in Hstep |- *; simpl in Hstep |- *.
          (* Hstep: dg_step (new_tree) x y, goal: dg_step (old_tree) x y *)
          unfold dg_step in Hstep |- *.
          destruct Hstep as [e [Hstep_orig [Hfst Hsnd]]].
          exists e. split; [| split; [exact Hfst | exact Hsnd]].
          (* Hstep_orig: original_step (new_tree) e, goal: original_step (old_tree) e *)
          unfold original_step in Hstep_orig |- *; simpl in Hstep_orig |- *.
          destruct Hstep_orig as [v [Hv_vis [Hfa_neq [Hfst_eq Hsnd_eq]]]].
          exists v. split; [exact Hv_vis |].
          simpl in Hfa_neq. unfold equiv_decb in Hfa_neq, Hfst_eq.
          destruct (equiv_dec v a) as [Heq | Hneq'].
          { exfalso. apply Hnv. rewrite <- Heq. exact Hv_vis. }
          { split; [exact Hfa_neq | split; [exact Hfst_eq | exact Hsnd_eq]]. }
        * (* fa_visited: set_fa a u may add fa a = u. u ∈ visited, so fa_visited holds. *)
          unfold fa_visited in Hfa_vis |- *.
          intros v Hfa_neq. simpl in Hfa_neq. simpl. unfold equiv_decb.
          unfold equiv_decb in Hfa_neq.
          destruct (equiv_dec v a) as [Heq | Hneq'].
          { (* v = a, fa = u, need u ∈ visited *) exact Huvis. }
          { (* v <> a, fa unchanged *) apply Hfa_vis. exact Hfa_neq. }
      + (* ~ a ∈ visited *) exact Hnv.
    - (* u ∈ visited *) exact Huvis.
    - (* In u (stack s) *) exact Hustack.
    - (* done_visited *) exact Hdonevis.
    - (* low_frontier *)
      unfold low_frontier in Hfront |- *.
      destruct Hfront as [Hle Hrest]. split; [exact Hle |].
      intros v Hdone_v Hdg_v.
      specialize (Hrest v Hdone_v Hdg_v).
      destruct Hrest as [Hfa_part Hstack_part].
      split.
      + simpl. unfold equiv_decb.
        destruct (equiv_dec v a) as [Heq | Hneq'].
        { exfalso. apply Hndone. rewrite <- Heq. exact Hdone_v. }
        { exact Hfa_part. }
      + exact Hstack_part.
    - (* low_src *)
      unfold low_src in Hsrc |- *.
      destruct Hsrc as [Hlow_eq | [(v & Hdone_v & Hdg_v & Hfa_eq & Hfa_neq_v & Hlow_eq) |
                                  (w & Hdone_w & Hdg_w & Hstk_w & Hfa_neq_w & Hlow_eq_w)]].
      + left. exact Hlow_eq.
      + right. left. exists v. simpl.
        split; [exact Hdone_v | split; [exact Hdg_v | split; [
          (* fa s v = u *)
          unfold equiv_decb; destruct (equiv_dec v a) as [Heq | Hneq'];
            [exfalso; apply Hndone; rewrite <- Heq; exact Hdone_v | exact Hfa_eq] |
          split; [
            (* fa s v <> v *)
            unfold equiv_decb; destruct (equiv_dec v a) as [Heq | Hneq'];
              [exfalso; apply Hndone; rewrite <- Heq; exact Hdone_v | exact Hfa_neq_v] |
            exact Hlow_eq]]]].
      + right. right. exists w. simpl.
        split; [exact Hdone_w | split; [exact Hdg_w | split; [
          exact Hstk_w | split; [
            unfold equiv_decb; destruct (equiv_dec w a) as [Heq | Hneq'];
              [exfalso; apply Hndone; rewrite <- Heq; exact Hdone_w |
               exact Hfa_neq_w] |
            exact Hlow_eq_w]]]].
    - (* children_low_valid: a is not visited, so changing fa a does not
         change the DFS tree seen by already visited/done children. *)
      unfold children_low_valid in Hchild |- *.
      intros v Hdone_v Hdg_v Hfa_eq Hfa_neq_v.
      simpl in Hfa_eq, Hfa_neq_v. unfold equiv_decb in Hfa_eq, Hfa_neq_v.
      destruct (equiv_dec v a) as [Heq | Hneq'].
      + exfalso. apply Hndone. rewrite <- Heq. exact Hdone_v.
      + apply (set_fa_preserves_scc_low_valid_v_when_unvisited v a u s0 Hnv).
        apply Hchild; auto.
    - (* fa_child_of_u *)
      unfold fa_child_of_u in Hfa_child |- *.
      intros v [Hfa_v Hfa_neq].
      simpl in Hfa_v, Hfa_neq. unfold equiv_decb in Hfa_v, Hfa_neq.
      destruct (equiv_dec v a) as [Heq | Hneq'].
      + (* v = a: new entry, we know dg_step g u a *)
        rewrite Heq. exact Hdg.
      + (* v <> a: existing entry, from Hfa_child *)
        apply (Hfa_child v). split; [exact Hfa_v | exact Hfa_neq].
    - (* fa s a = u *)
      simpl. unfold equiv_decb.
      destruct (equiv_dec a a) as [_ | Hc]; [reflexivity | exfalso; apply Hc; reflexivity].
  Qed.

  (* ================================================================ *)
  (* Pop phase contracts                                             *)
  (* ================================================================ *)

  Lemma pop_scc_preserves_low_valid_post_when_root
        (u: V):
    Hoare (fun s: @SCCSt V =>
             low_iteration_done g root u s /\
             scc_low_valid_v g root s u /\
             low s u = dfn s u)
          (pop_scc u)
          (fun _ s => low_valid_post g root u s /\
                      u ∈ visited s /\
                      stack_dfn_order s /\
                      dfn_injective s).
  Proof.
    unfold low_valid_post, low_iteration_done.
    unfold pop_scc. intro_state. hoare_auto_s.
    subst s. unfold pop_scc_state.
    destruct (stack_split_at (stack s0) u) as [popped rest] eqn:Hsplit.
    simpl.
    destruct H as [[Hiter [Horder Hinj]] [Hscc Hlow_dfn]].
    destruct Hiter as (Hwf & Huvis & Hustack & Hdonevis & Hfront & Hsrc & Hchild & Hfa_child & Hfa_not).
    split; [| split; [| split; [| ]]].
    { (* wf_scc_state /\ scc_low_valid_v *)
      split.
      { (* wf_scc_state *)
        unfold wf_scc_state in Hwf |- *.
        destruct Hwf as [Hsiv [Hinv [Hvalid Hfa_vis]]].
        split; [| split; [| split; [| ]]].
        - (* stack_in_visited *)
          unfold stack_in_visited in Hsiv |- *.
          intros w Hw. simpl in Hw.
          apply Hsiv.
          destruct (stack_split_at_decomp (stack s0) u Hustack popped rest Hsplit) as [prefix Hstk_eq].
          rewrite Hstk_eq. rewrite List.in_app_iff. right. right. exact Hw.
        - (* dfn_inv *) exact Hinv.
        - (* dfn_valid *)
          unfold dfn_valid in Hvalid |- *.
          intros x y Hstep.
          apply Hvalid.
          unfold state_to_dfs_tree in Hstep |- *.
          simpl in Hstep |- *.
          exact Hstep.
        - (* fa_visited *) exact Hfa_vis. }
      { (* scc_low_valid_v *)
        unfold scc_low_valid_v, min_value_of_subset, min_object_of_subset in *.
        exists (low s0 u). split.
        - split.
          + right.
            exists u. split.
            * split.
              -- sets_unfold. right. reflexivity.
              -- intros x Hx. sets_unfold in Hx.
                 destruct Hx as [Hback | Heq_x].
                 ++ destruct Hback as [Hdg_x [Hstack_x _]].
                    simpl in *.
                    rewrite <- Hlow_dfn.
                    unfold low_frontier in Hfront.
                    destruct Hfront as [_ Hfront].
                    specialize (Hfront x Hdg_x Hdg_x) as [_ Hstack_part].
                    apply Hstack_part.
                    destruct (stack_split_at_decomp (stack s0) u Hustack popped rest Hsplit)
                      as [prefix Hstk_eq].
                    rewrite Hstk_eq, List.in_app_iff.
                    right. simpl. right. exact Hstack_x.
                 ++ subst x. apply le_n.
            * symmetry. exact Hlow_dfn.
          + intros n Hn. destruct Hn as [Hchild_min | Hback_min].
            * destruct Hscc as [old_n [[Hold_mem Hold_bound] Hold_eq]].
              assert (Hold_mem_child :
                        min_value_of_subset Nat.le
                          (dg_step (state_to_dfs_tree g s0 root) u) (low s0) n).
              { unfold min_value_of_subset, min_object_of_subset in Hchild_min |- *.
                destruct Hchild_min as [x [[Htree_x Hmin_x] Hn_eq]].
                exists x. split; [| exact Hn_eq].
                split.
                - unfold state_to_dfs_tree in Htree_x |- *.
                  simpl in Htree_x |- *. exact Htree_x.
                - intros y Hy.
                  apply Hmin_x.
                  unfold state_to_dfs_tree in Hy |- *.
                  simpl in Hy |- *. exact Hy. }
              rewrite <- Hold_eq.
              apply Hold_bound. left. exact Hold_mem_child.
            * unfold min_value_of_subset, min_object_of_subset in Hback_min.
              destruct Hback_min as [x [[Hx _] Hn_eq]].
              subst n. sets_unfold in Hx.
              destruct Hx as [Hback | Heq_x].
              -- destruct Hback as [Hdg_x [Hstack_x _]].
                 simpl in *.
                 unfold low_frontier in Hfront.
                 destruct Hfront as [_ Hfront].
                 specialize (Hfront x Hdg_x Hdg_x) as [_ Hstack_part].
                 apply Hstack_part.
                 destruct (stack_split_at_decomp (stack s0) u Hustack popped rest Hsplit)
                   as [prefix Hstk_eq].
                 rewrite Hstk_eq, List.in_app_iff.
                 right. simpl. right. exact Hstack_x.
              -- subst x. rewrite Hlow_dfn. apply le_n.
        - reflexivity. } }
    { (* u ∈ visited *) exact Huvis. }
    { (* stack_dfn_order *)
      unfold stack_dfn_order. simpl.
      intros x y Hx_in Hy_in [l1 [l2 [Hrest_eq Hy_in_l2]]].
      destruct (stack_split_at_decomp (stack s0) u Hustack popped rest Hsplit) as [prefix Hstk_eq].
      apply (Horder x y).
      - rewrite Hstk_eq, List.in_app_iff. right. simpl. right. exact Hx_in.
      - rewrite Hstk_eq, List.in_app_iff. right. simpl. right. exact Hy_in.
      - exists (prefix ++ u :: l1). exists l2. split.
        { rewrite Hstk_eq, Hrest_eq. rewrite <- app_assoc. reflexivity. }
        { exact Hy_in_l2. } }
    { (* dfn_injective *) exact Hinj. }
  Qed.

  Lemma if_pop_preserves_low_valid_post (u: V):
    Hoare (fun s: @SCCSt V =>
             low_iteration_done g root u s /\
             scc_low_valid_v g root s u)
          (If (fun s => low s u = dfn s u) (pop_scc u))
          (fun _ s => low_valid_post g root u s /\
                      u ∈ visited s /\
                      stack_dfn_order s /\
                      dfn_injective s).
  Proof.
    unfold If. intro_state. hoare_auto_s.
    { (* Branch: low s0 u = dfn s0 u, execute pop_scc *)
      eapply Hoare_conseq_pre.
      2: { apply pop_scc_preserves_low_valid_post_when_root. }
      intros s Heq. subst s.
      destruct H as [Hdone Hscc].
      split; [exact Hdone | split; [exact Hscc | exact H1]]. }
    { (* Branch: low s0 u <> dfn s0 u, skip *)
      destruct H1 as [Heq _]. subst s.
      unfold low_valid_post, low_iteration_done.
      destruct H as [Hiter Hscc].
      destruct Hiter as [Hinv [Horder Hinj]].
      destruct Hinv as (Hwf & Huvis & Hustack & Hdonevis & Hfront & Hsrc & Hchild & Hfa_child & Hfa_not).
      split; [split; [exact Hwf | exact Hscc] | split; [exact Huvis | split; [exact Horder | exact Hinj]]]. }
  Qed.

End LOW_PRIMITIVES.
