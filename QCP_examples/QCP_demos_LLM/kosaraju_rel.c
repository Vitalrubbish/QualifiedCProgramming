#include "safeexecE_def.h"
#include "verification_stdlib.h"
#include "int_array_def.h"

/*@ Import Coq Require Import SimpleC.EE.QCP_demos_LLM.kosaraju_rel_lib */

/*@ Extern Coq (KSt :: *) (AdjGraph :: *) (unit :: *) */
/*@ Extern Coq
               (dfs_finish: AdjGraph -> Z -> program KSt unit)
               (dfs_scc: AdjGraph -> Z -> Z -> program KSt unit)
               (dfs_finish_from: AdjGraph -> list Z -> list Z -> Z -> Z -> program KSt unit)
               (dfs_scc_from: AdjGraph -> list Z -> list Z -> Z -> Z -> Z -> program KSt unit)
               (dfs_finish_fromK: AdjGraph -> list Z -> list Z -> Z -> Z -> unit -> program KSt unit)
               (dfs_scc_fromK: AdjGraph -> list Z -> list Z -> Z -> Z -> Z -> unit -> program KSt unit)
               (pre_dfs1: AdjGraph -> list Z -> list Z -> list Z -> list Z -> Z -> KSt -> Prop)
               (pre_dfs2: AdjGraph -> list Z -> list Z -> list Z -> list Z -> Z -> KSt -> Prop)
               (csr_wf1: AdjGraph -> list Z -> list Z -> list Z -> list Z -> Prop)
               (csr_wf2: AdjGraph -> list Z -> list Z -> list Z -> list Z -> Prop)
               (radj_col_particular: AdjGraph -> list Z -> Prop)
               (csr1_faithful: AdjGraph -> list Z -> list Z -> Prop)
               (csr2_faithful: AdjGraph -> list Z -> list Z -> Prop)
               (adj_verts: AdjGraph -> Z)
               (m_of: list Z -> Z)
               (csr_lo: Z -> list Z -> Z)
               (csr_hi: Z -> list Z -> Z)
               (count_nonzero: list Z -> Z)
               (Znth: {A} -> Z -> list A -> A -> A)
               (replace_Znth: {A} -> Z -> A -> list A -> list A)
                */

/* ==================================================================== */
/* dfs1: reverse-graph DFS (phase 1).  Walks the reverse graph in CSR   */
/* layout: vertex u's in-neighbours are radj_col[radj_row[u] ..         */
/* radj_row[u+1]-1].  On finish, records finish time fin[u] = timer++.  */
/*                                                                      */
/* CSR layout (all IntArray, handled by int_array strategy):            */
/*   radj_col : length m_of(radj_row_l), the packed neighbour array     */
/*   radj_row : length n+1, the per-vertex offset array                 */
/*   vis1/fin : length n;  timer_p : length 1                           */
/*                                                                      */
/* Refines the abstract monad  dfs_finish u  (Kosaraju.v:DFS_finish).   */
/* The loop continuation is  dfs_finish_from(radj_col_l, radj_row_l,    */
/* u, i)  with i the CSR cursor; this is designed/validated in the      */
/* annotation phase on annotation_scratch_lib.                          */
/* ==================================================================== */
void dfs1(int u, int n,
          int *radj_col, int *radj_row,
          int *vis1, int *fin, int *timer_p)
/*@ bind_spec <= low_level_spec
    With {B} g radj_col_l radj_row_l vis1_l fin_l timer_v X (f: unit -> program KSt B)
    Require
      csr_wf1(g, radj_col_l, radj_row_l, vis1_l, fin_l) &&
      adj_verts(g) == n &&
      safeExec(pre_dfs1(g, radj_col_l, radj_row_l, vis1_l, fin_l, timer_v),
               bind(dfs_finish(g, u), f), X) &&
      0 <= u && u < n && n <= 2147483647 &&
      Znth(u, vis1_l, 0) == 0 &&
      0 <= timer_v && timer_v <= count_nonzero(vis1_l) &&
      IntArray::full(radj_col, m_of(radj_row_l), radj_col_l) *
      IntArray::full(radj_row, n + 1, radj_row_l) *
      IntArray::full(vis1, n, vis1_l) *
      IntArray::full(fin, n, fin_l) *
      IntArray::full(timer_p, 1, cons(timer_v, nil))
    Ensure
      exists vis1_l_ fin_l_ timer_v_,
      csr_wf1(g, radj_col_l, radj_row_l, vis1_l_, fin_l_) &&
      adj_verts(g) == n &&
      safeExec(pre_dfs1(g, radj_col_l, radj_row_l, vis1_l_, fin_l_, timer_v_),
               applyf(f, tt), X) &&
      0 <= timer_v_ &&
      count_nonzero(vis1_l_) - timer_v_ == count_nonzero(vis1_l) - timer_v &&
      IntArray::full(radj_col, m_of(radj_row_l), radj_col_l) *
      IntArray::full(radj_row, n + 1, radj_row_l) *
      IntArray::full(vis1, n, vis1_l_) *
      IntArray::full(fin, n, fin_l_) *
      IntArray::full(timer_p, 1, cons(timer_v_, nil))
*/;
void dfs1(int u, int n,
          int *radj_col, int *radj_row,
          int *vis1, int *fin, int *timer_p)
/*@ low_level_spec
    With g radj_col_l radj_row_l vis1_l fin_l timer_v X
    Require
      csr_wf1(g, radj_col_l, radj_row_l, vis1_l, fin_l) &&
      adj_verts(g) == n &&
      safeExec(pre_dfs1(g, radj_col_l, radj_row_l, vis1_l, fin_l, timer_v),
               dfs_finish(g, u), X) &&
      0 <= u && u < n && n <= 2147483647 &&
      Znth(u, vis1_l, 0) == 0 &&
      0 <= timer_v && timer_v <= count_nonzero(vis1_l) &&
      IntArray::full(radj_col, m_of(radj_row_l), radj_col_l) *
      IntArray::full(radj_row, n + 1, radj_row_l) *
      IntArray::full(vis1, n, vis1_l) *
      IntArray::full(fin, n, fin_l) *
      IntArray::full(timer_p, 1, cons(timer_v, nil))
    Ensure
      exists vis1_l_ fin_l_ timer_v_,
      csr_wf1(g, radj_col_l, radj_row_l, vis1_l_, fin_l_) &&
      adj_verts(g) == n &&
      safeExec(pre_dfs1(g, radj_col_l, radj_row_l, vis1_l_, fin_l_, timer_v_),
               return(tt), X) &&
      0 <= timer_v_ &&
      count_nonzero(vis1_l_) - timer_v_ == count_nonzero(vis1_l) - timer_v &&
      IntArray::full(radj_col, m_of(radj_row_l), radj_col_l) *
      IntArray::full(radj_row, n + 1, radj_row_l) *
      IntArray::full(vis1, n, vis1_l_) *
      IntArray::full(fin, n, fin_l_) *
      IntArray::full(timer_p, 1, cons(timer_v_, nil))
 */
{
  vis1[u] = 1;
  int lo = radj_row[u];
  int hi = radj_row[u + 1];
  int i = lo;

  /*@ Inv Assert
      exists vis1_m fin_m timer_m,
        csr_wf1(g, radj_col_l, radj_row_l, vis1_m, fin_m) &&
        adj_verts(g) == n &&
        safeExec(pre_dfs1(g, radj_col_l, radj_row_l, vis1_m, fin_m, timer_m),
                 dfs_finish_from(g, radj_col_l, radj_row_l, u, i), X) &&
        u == u@pre && n == n@pre &&
        radj_col == radj_col@pre && radj_row == radj_row@pre &&
        vis1 == vis1@pre && fin == fin@pre && timer_p == timer_p@pre &&
        lo == csr_lo(u, radj_row_l) && hi == csr_hi(u, radj_row_l) &&
        0 <= lo && lo <= i && i <= hi && hi <= m_of(radj_row_l) &&
        0 <= u && u < n && n <= 2147483647 &&
        0 <= timer_m && timer_m < count_nonzero(vis1_m) &&
        IntArray::full(radj_col, m_of(radj_row_l), radj_col_l) *
        IntArray::full(radj_row, n + 1, radj_row_l) *
        IntArray::full(vis1, n, vis1_m) *
        IntArray::full(fin, n, fin_m) *
        IntArray::full(timer_p, 1, cons(timer_m, nil))
  */
  while (i < hi) {
    /*@ Given vis1_m fin_m timer_m */
    int v;
    v = radj_col[i];

    /*@ Assert
        csr_wf1(g, radj_col_l, radj_row_l, vis1_m, fin_m) &&
        adj_verts(g) == n &&
        safeExec(pre_dfs1(g, radj_col_l, radj_row_l, vis1_m, fin_m, timer_m),
                 dfs_finish_from(g, radj_col_l, radj_row_l, u, i), X) &&
        u == u@pre && n == n@pre &&
        radj_col == radj_col@pre && radj_row == radj_row@pre &&
        vis1 == vis1@pre && fin == fin@pre && timer_p == timer_p@pre &&
        lo == csr_lo(u, radj_row_l) && hi == csr_hi(u, radj_row_l) &&
        0 <= lo && lo <= i && i < hi && hi <= m_of(radj_row_l) &&
        0 <= u && u < n && n <= 2147483647 &&
        0 <= timer_m && timer_m < count_nonzero(vis1_m) &&
        0 <= v && v < n && v == Znth(i, radj_col_l, 0) &&
        IntArray::full(radj_col, m_of(radj_row_l), radj_col_l) *
        IntArray::full(radj_row, n + 1, radj_row_l) *
        IntArray::full(vis1, n, vis1_m) *
        IntArray::full(fin, n, fin_m) *
        IntArray::full(timer_p, 1, cons(timer_m, nil))
        */

    if (vis1[v] == 0) {
      dfs1(v, n, radj_col, radj_row, vis1, fin, timer_p)
          /*@ where(bind_spec)
                g = g,
                radj_col_l = radj_col_l, radj_row_l = radj_row_l,
                vis1_l = vis1_m, fin_l = fin_m, timer_v = timer_m,
                X = X,
                f = dfs_finish_fromK(g, radj_col_l, radj_row_l, u, i + 1); B = unit */;
    }
    i = i + 1;
  }

  {
    int t0 = timer_p[0];
    fin[u] = t0;
    timer_p[0] = t0 + 1;
  }
}

/* ==================================================================== */
/* dfs2: forward-graph DFS (phase 2).  Walks the forward graph in CSR   */
/* layout: vertex u's out-neighbours are fadj_col[fadj_row[u] ..        */
/* fadj_row[u+1]-1].  Marks sid[u] = sid[root] for the whole SCC.       */
/* No finish-time bookkeeping (phase 2 only assigns SCC ids).           */
/* Refines the abstract monad  dfs_scc root u  (Kosaraju.v:DFS_scc).    */
/* ==================================================================== */
void dfs2(int root, int u, int n,
          int *fadj_col, int *fadj_row,
          int *vis2, int *sid)
/*@ bind_spec <= low_level_spec
    With {B} g fadj_col_l fadj_row_l vis2_l sid_l root_v X (f: unit -> program KSt B)
    Require
      csr_wf2(g, fadj_col_l, fadj_row_l, vis2_l, sid_l) &&
      csr2_faithful(g, fadj_col_l, fadj_row_l) &&
      adj_verts(g) == n &&
      safeExec(pre_dfs2(g, fadj_col_l, fadj_row_l, vis2_l, sid_l, root_v),
               bind(dfs_scc(g, root, u), f), X) &&
      0 <= u && u < n && 0 <= root && root < n && n <= 2147483647 &&
      Znth(root, vis2_l, 0) != 0 &&
      IntArray::full(fadj_col, m_of(fadj_row_l), fadj_col_l) *
      IntArray::full(fadj_row, n + 1, fadj_row_l) *
      IntArray::full(vis2, n, vis2_l) *
      IntArray::full(sid, n, sid_l)
    Ensure
      exists vis2_l_ sid_l_,
      csr_wf2(g, fadj_col_l, fadj_row_l, vis2_l_, sid_l_) &&
      adj_verts(g) == n &&
      safeExec(pre_dfs2(g, fadj_col_l, fadj_row_l, vis2_l_, sid_l_, root_v),
               applyf(f, tt), X) &&
      Znth(u, vis2_l_, 0) != 0 &&
      Znth(u, sid_l_, 0) == Znth(root, sid_l_, 0) &&
      (forall (w: Z), (0 <= w && w < n) =>
                  (Znth(w, vis2_l, 0) != 0 => Znth(w, vis2_l_, 0) != 0)) &&
      (forall (w: Z), (0 <= w && w < n) =>
                  (Znth(w, vis2_l, 0) != 0 => Znth(w, sid_l, 0) == Znth(w, sid_l_, 0))) &&
      IntArray::full(fadj_col, m_of(fadj_row_l), fadj_col_l) *
      IntArray::full(fadj_row, n + 1, fadj_row_l) *
      IntArray::full(vis2, n, vis2_l_) *
      IntArray::full(sid, n, sid_l_)
*/;
void dfs2(int root, int u, int n,
          int *fadj_col, int *fadj_row,
          int *vis2, int *sid)
/*@ low_level_spec
    With g fadj_col_l fadj_row_l vis2_l sid_l root_v X
    Require
      csr_wf2(g, fadj_col_l, fadj_row_l, vis2_l, sid_l) &&
      csr2_faithful(g, fadj_col_l, fadj_row_l) &&
      adj_verts(g) == n &&
      safeExec(pre_dfs2(g, fadj_col_l, fadj_row_l, vis2_l, sid_l, root_v),
               dfs_scc(g, root, u), X) &&
      0 <= u && u < n && 0 <= root && root < n && n <= 2147483647 &&
      Znth(root, vis2_l, 0) != 0 &&
      IntArray::full(fadj_col, m_of(fadj_row_l), fadj_col_l) *
      IntArray::full(fadj_row, n + 1, fadj_row_l) *
      IntArray::full(vis2, n, vis2_l) *
      IntArray::full(sid, n, sid_l)
    Ensure
      exists vis2_l_ sid_l_,
      csr_wf2(g, fadj_col_l, fadj_row_l, vis2_l_, sid_l_) &&
      adj_verts(g) == n &&
      safeExec(pre_dfs2(g, fadj_col_l, fadj_row_l, vis2_l_, sid_l_, root_v),
               return(tt), X) &&
      Znth(u, vis2_l_, 0) != 0 &&
      Znth(u, sid_l_, 0) == Znth(root, sid_l_, 0) &&
      (forall (w: Z), (0 <= w && w < n) =>
                  (Znth(w, vis2_l, 0) != 0 => Znth(w, vis2_l_, 0) != 0)) &&
      (forall (w: Z), (0 <= w && w < n) =>
                  (Znth(w, vis2_l, 0) != 0 => Znth(w, sid_l, 0) == Znth(w, sid_l_, 0))) &&
      IntArray::full(fadj_col, m_of(fadj_row_l), fadj_col_l) *
      IntArray::full(fadj_row, n + 1, fadj_row_l) *
      IntArray::full(vis2, n, vis2_l_) *
      IntArray::full(sid, n, sid_l_)
 */
{
  vis2[u] = 1;
  sid[u] = sid[root];
  int lo = fadj_row[u];
  int hi = fadj_row[u + 1];
  int i = lo;

  /*@ Inv Assert
      exists vis2_m sid_m,
        csr_wf2(g, fadj_col_l, fadj_row_l, vis2_m, sid_m) &&
        csr2_faithful(g, fadj_col_l, fadj_row_l) &&
        adj_verts(g) == n &&
        safeExec(pre_dfs2(g, fadj_col_l, fadj_row_l, vis2_m, sid_m, root_v),
                 dfs_scc_from(g, fadj_col_l, fadj_row_l, root, u, i), X) &&
        root == root@pre && u == u@pre && n == n@pre &&
        fadj_col == fadj_col@pre && fadj_row == fadj_row@pre &&
        vis2 == vis2@pre && sid == sid@pre &&
        lo == csr_lo(u, fadj_row_l) && hi == csr_hi(u, fadj_row_l) &&
        0 <= lo && lo <= i && i <= hi && hi <= m_of(fadj_row_l) &&
        0 <= u && u < n && 0 <= root && root < n && n <= 2147483647 &&
        Znth(u, vis2_m, 0) != 0 &&
        Znth(u, sid_m, 0) == Znth(root, sid_m, 0) &&
        (forall (j: Z), (lo <= j && j < i) =>
                    (Znth(Znth(j, fadj_col_l, 0), vis2_m, 0) != 0)) &&
        Znth(root, vis2_m, 0) != 0 &&
        (forall (w: Z), (0 <= w && w < n) =>
                    (Znth(w, vis2_l, 0) != 0 => Znth(w, vis2_m, 0) != 0)) &&
        (forall (w: Z), (0 <= w && w < n) =>
                    (w != u => Znth(w, vis2_l, 0) != 0 => Znth(w, sid_l, 0) == Znth(w, sid_m, 0))) &&
        IntArray::full(fadj_col, m_of(fadj_row_l), fadj_col_l) *
        IntArray::full(fadj_row, n + 1, fadj_row_l) *
        IntArray::full(vis2, n, vis2_m) *
        IntArray::full(sid, n, sid_m)
  */
  while (i < hi) {
    /*@ Given vis2_m sid_m */
    int v;
    v = fadj_col[i];

    /*@ Assert
        csr_wf2(g, fadj_col_l, fadj_row_l, vis2_m, sid_m) &&
        csr2_faithful(g, fadj_col_l, fadj_row_l) &&
        adj_verts(g) == n &&
        safeExec(pre_dfs2(g, fadj_col_l, fadj_row_l, vis2_m, sid_m, root_v),
                 dfs_scc_from(g, fadj_col_l, fadj_row_l, root, u, i), X) &&
        root == root@pre && u == u@pre && n == n@pre &&
        fadj_col == fadj_col@pre && fadj_row == fadj_row@pre &&
        vis2 == vis2@pre && sid == sid@pre &&
        lo == csr_lo(u, fadj_row_l) && hi == csr_hi(u, fadj_row_l) &&
        0 <= lo && lo <= i && i < hi && hi <= m_of(fadj_row_l) &&
        0 <= u && u < n && 0 <= root && root < n && n <= 2147483647 &&
        Znth(u, vis2_m, 0) != 0 &&
        Znth(u, sid_m, 0) == Znth(root, sid_m, 0) &&
        (forall (j: Z), (lo <= j && j < i) =>
                    (Znth(Znth(j, fadj_col_l, 0), vis2_m, 0) != 0)) &&
        Znth(root, vis2_m, 0) != 0 &&
        (forall (w: Z), (0 <= w && w < n) =>
                    (Znth(w, vis2_l, 0) != 0 => Znth(w, vis2_m, 0) != 0)) &&
        (forall (w: Z), (0 <= w && w < n) =>
                    (w != u => Znth(w, vis2_l, 0) != 0 => Znth(w, sid_l, 0) == Znth(w, sid_m, 0))) &&
        0 <= v && v < n && v == Znth(i, fadj_col_l, 0) &&
        IntArray::full(fadj_col, m_of(fadj_row_l), fadj_col_l) *
        IntArray::full(fadj_row, n + 1, fadj_row_l) *
        IntArray::full(vis2, n, vis2_m) *
        IntArray::full(sid, n, sid_m)
    */
    if (vis2[v] == 0) {
      dfs2(root, v, n, fadj_col, fadj_row, vis2, sid)
          /*@ where(bind_spec)
                g = g,
                fadj_col_l = fadj_col_l, fadj_row_l = fadj_row_l,
                vis2_l = vis2_m, sid_l = sid_m, root_v = root_v,
                X = X,
                f = dfs_scc_fromK(g, fadj_col_l, fadj_row_l, root, u, i + 1); B = unit */;
    }
    i = i + 1;
  }
}
