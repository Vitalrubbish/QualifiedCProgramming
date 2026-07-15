#include "safeexecE_def.h"
#include "verification_stdlib.h"
#include "int_array_def.h"

/*@ Import Coq Require Import SimpleC.EE.QCP_demos_LLM.kosaraju_rel_lib */

/*@ Extern Coq (KSt :: *) (AdjGraph :: *) (unit :: *) */
/*@ Extern Coq
               (mutually_reachable: AdjGraph -> Z -> Z -> Prop)
               (order_spec: list Z -> list Z -> Z -> Prop)
               (transpose_spec: AdjGraph -> list Z -> list Z -> list Z -> list Z -> Z -> Prop)
               (dfs1_high_level_post: AdjGraph -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> Z -> Z -> Z -> Z -> Prop)
               (dfs2_high_level_post: AdjGraph -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> Z -> Z -> Z -> Prop)
               (AdjGraphValid: AdjGraph -> Prop)
                */
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

/* Working-array allocator / deallocator (clone of kmp_rel.c:25-36). */
int * malloc_int_array(int n)
  /*@ Require n > 0 && emp
      Ensure exists l, IntArray::full(__return, n, l)
   */
  ;

void free_int_array(int *a)
  /*@ With n l
      Require IntArray::full(a, n, l)
      Ensure emp
   */
  ;

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
/*@ high_level_spec <= low_level_spec
    With g radj_col_l radj_row_l vis1_l fin_l timer_v
    Require
      csr_wf1(g, radj_col_l, radj_row_l, vis1_l, fin_l) &&
      csr1_faithful(g, radj_col_l, radj_row_l) &&
      adj_verts(g) == n &&
      0 <= u && u < n && n <= 2147483647 &&
      Znth(u, vis1_l, 0) == 0 &&
      0 <= timer_v &&
      IntArray::full(radj_col, m_of(radj_row_l), radj_col_l) *
      IntArray::full(radj_row, n + 1, radj_row_l) *
      IntArray::full(vis1, n, vis1_l) *
      IntArray::full(fin, n, fin_l) *
      IntArray::full(timer_p, 1, cons(timer_v, nil))
    Ensure
      exists vis1_l_ fin_l_ timer_v_,
      dfs1_high_level_post(g, radj_col_l, radj_row_l,
                              vis1_l, fin_l, vis1_l_, fin_l_,
                              u, timer_v, timer_v_, n) &&
      adj_verts(g) == n &&
      IntArray::full(radj_col, m_of(radj_row_l), radj_col_l) *
      IntArray::full(radj_row, n + 1, radj_row_l) *
      IntArray::full(vis1, n, vis1_l_) *
      IntArray::full(fin, n, fin_l_) *
      IntArray::full(timer_p, 1, cons(timer_v_, nil))
*/;
void dfs1(int u, int n,
          int *radj_col, int *radj_row,
          int *vis1, int *fin, int *timer_p)
/*@ bind_spec <= low_level_spec
    With {B} g radj_col_l radj_row_l vis1_l fin_l timer_v X (f: unit -> program KSt B)
    Require
      csr_wf1(g, radj_col_l, radj_row_l, vis1_l, fin_l) &&
      csr1_faithful(g, radj_col_l, radj_row_l) &&
      adj_verts(g) == n &&
      safeExec(pre_dfs1(g, radj_col_l, radj_row_l, vis1_l, fin_l, timer_v),
               bind(dfs_finish(g, u), f), X) &&
      0 <= u && u < n && n <= 2147483647 &&
      Znth(u, vis1_l, 0) == 0 &&
      0 <= timer_v &&
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
      csr1_faithful(g, radj_col_l, radj_row_l) &&
      adj_verts(g) == n &&
      safeExec(pre_dfs1(g, radj_col_l, radj_row_l, vis1_l, fin_l, timer_v),
               dfs_finish(g, u), X) &&
      0 <= u && u < n && n <= 2147483647 &&
      Znth(u, vis1_l, 0) == 0 &&
      0 <= timer_v &&
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
        csr1_faithful(g, radj_col_l, radj_row_l) &&
        adj_verts(g) == n &&
        safeExec(pre_dfs1(g, radj_col_l, radj_row_l, vis1_m, fin_m, timer_m),
                 dfs_finish_from(g, radj_col_l, radj_row_l, u, i), X) &&
        u == u@pre && n == n@pre &&
        radj_col == radj_col@pre && radj_row == radj_row@pre &&
        vis1 == vis1@pre && fin == fin@pre && timer_p == timer_p@pre &&
        lo == csr_lo(u, radj_row_l) && hi == csr_hi(u, radj_row_l) &&
        0 <= lo && lo <= i && i <= hi && hi <= m_of(radj_row_l) &&
        0 <= u && u < n && n <= 2147483647 &&
        0 <= timer_m &&
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
        csr1_faithful(g, radj_col_l, radj_row_l) &&
        adj_verts(g) == n &&
        safeExec(pre_dfs1(g, radj_col_l, radj_row_l, vis1_m, fin_m, timer_m),
                 dfs_finish_from(g, radj_col_l, radj_row_l, u, i), X) &&
        u == u@pre && n == n@pre &&
        radj_col == radj_col@pre && radj_row == radj_row@pre &&
        vis1 == vis1@pre && fin == fin@pre && timer_p == timer_p@pre &&
        lo == csr_lo(u, radj_row_l) && hi == csr_hi(u, radj_row_l) &&
        0 <= lo && lo <= i && i < hi && hi <= m_of(radj_row_l) &&
        0 <= u && u < n && n <= 2147483647 &&
        0 <= timer_m &&
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
/*@ high_level_spec <= low_level_spec
    With g fadj_col_l fadj_row_l vis2_l sid_l
    Require
      csr_wf2(g, fadj_col_l, fadj_row_l, vis2_l, sid_l) &&
      csr2_faithful(g, fadj_col_l, fadj_row_l) &&
      adj_verts(g) == n &&
      0 <= u && u < n && 0 <= root && root < n && n <= 2147483647 &&
      Znth(root, vis2_l, 0) != 0 &&
      IntArray::full(fadj_col, m_of(fadj_row_l), fadj_col_l) *
      IntArray::full(fadj_row, n + 1, fadj_row_l) *
      IntArray::full(vis2, n, vis2_l) *
      IntArray::full(sid, n, sid_l)
    Ensure
      exists vis2_l_ sid_l_,
      dfs2_high_level_post(g, fadj_col_l, fadj_row_l,
                              vis2_l, sid_l, vis2_l_, sid_l_,
                              root, u, n) &&
      adj_verts(g) == n &&
      IntArray::full(fadj_col, m_of(fadj_row_l), fadj_col_l) *
      IntArray::full(fadj_row, n + 1, fadj_row_l) *
      IntArray::full(vis2, n, vis2_l_) *
      IntArray::full(sid, n, sid_l_)
*/;
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
      (forall (w: Z), (0 <= w && w < n) =>
                  (Znth(w, vis2_l, 0) != 0 => Znth(w, vis2_l_, 0) != 0)) &&
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
      (forall (w: Z), (0 <= w && w < n) =>
                  (Znth(w, vis2_l, 0) != 0 => Znth(w, vis2_l_, 0) != 0)) &&
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
        (forall (j: Z), (lo <= j && j < i) =>
                    (Znth(Znth(j, fadj_col_l, 0), vis2_m, 0) != 0)) &&
        Znth(root, vis2_m, 0) != 0 &&
        (forall (w: Z), (0 <= w && w < n) =>
                    (Znth(w, vis2_l, 0) != 0 => Znth(w, vis2_m, 0) != 0)) &&
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
        (forall (j: Z), (lo <= j && j < i) =>
                    (Znth(Znth(j, fadj_col_l, 0), vis2_m, 0) != 0)) &&
        Znth(root, vis2_m, 0) != 0 &&
        (forall (w: Z), (0 <= w && w < n) =>
                    (Znth(w, vis2_l, 0) != 0 => Znth(w, vis2_m, 0) != 0)) &&
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

/* ==================================================================== */
/* transpose: counting-sort CSR transpose of the forward graph.        */
/*   Inputs : fadj_col[fadj_row[u] .. fadj_row[u+1]-1] = out-neighbours*/
/*            of u, i.e. forward edges (u -> v) packed in CSR.         */
/*   Outputs: radj_col/radj_row = reverse CSR, where radj_col          */
/*            [radj_row[v] .. radj_row[v+1]-1] = in-neighbours of v    */
/*            = { u | edge u->v }.                                      */
/*   pos   : scratch cursor array of length n (malloc'd by caller),    */
/*           used as the moving write head during the scatter pass so  */
/*           radj_row stays in prefix-sum (offset) form.               */
/*   Algorithm (standard CSR transpose):                                */
/*     pass 1: count in-degree of each v into radj_row[0..n-1]          */
/*     pass 2: prefix-sum radj_row (radj_row[v]=bucket start of v);    */
/*             radj_row[n] = m.  Copy radj_row -> pos (write heads).    */
/*     pass 3: for each vertex u, scan its forward neighbour range; for */
/*             each edge (u,v) write u at radj_col[pos[v]], pos[v]++.   */
/*             The outer loop carries u, so no CSR inverse lookup.     */
/*   Postcondition: transpose_spec (csr1_faithful + csr_wf1).          */
/*   high_level_spec <= low_level_spec (no monad; pure arrays).         */
/* ==================================================================== */
void transpose(int n, int m,
               int *fadj_col, int *fadj_row,
               int *radj_col, int *radj_row, int *pos)
/*@ high_level_spec <= low_level_spec
    With g fadj_col_l fadj_row_l radj_col_l radj_row_l pos_l
    Require
      1 <= n && n <= 2147483647 &&
      m == m_of(fadj_row_l) &&
      csr2_faithful(g, fadj_col_l, fadj_row_l) &&
      AdjGraphValid(g) &&
      adj_verts(g) == n &&
      IntArray::full(fadj_col, m_of(fadj_row_l), fadj_col_l) *
      IntArray::full(fadj_row, n + 1, fadj_row_l) *
      IntArray::full(radj_col, m_of(fadj_row_l), radj_col_l) *
      IntArray::full(radj_row, n + 1, radj_row_l) *
      IntArray::full(pos, n, pos_l)
    Ensure
      exists radj_col_l_ radj_row_l_ pos_l_,
      transpose_spec(g, fadj_col_l, fadj_row_l, radj_col_l_, radj_row_l_, n) &&
      IntArray::full(fadj_col, m_of(fadj_row_l), fadj_col_l) *
      IntArray::full(fadj_row, n + 1, fadj_row_l) *
      IntArray::full(radj_col, m_of(fadj_row_l), radj_col_l_) *
      IntArray::full(radj_row, n + 1, radj_row_l_) *
      IntArray::full(pos, n, pos_l_)
*/;
void transpose(int n, int m,
               int *fadj_col, int *fadj_row,
               int *radj_col, int *radj_row, int *pos)
/*@ low_level_spec
    With g fadj_col_l fadj_row_l radj_col_l radj_row_l pos_l
    Require
      1 <= n && n <= 2147483647 &&
      m == m_of(fadj_row_l) &&
      csr2_faithful(g, fadj_col_l, fadj_row_l) &&
      AdjGraphValid(g) &&
      adj_verts(g) == n &&
      IntArray::full(fadj_col, m_of(fadj_row_l), fadj_col_l) *
      IntArray::full(fadj_row, n + 1, fadj_row_l) *
      IntArray::full(radj_col, m_of(fadj_row_l), radj_col_l) *
      IntArray::full(radj_row, n + 1, radj_row_l) *
      IntArray::full(pos, n, pos_l)
    Ensure
      exists radj_col_l_ radj_row_l_ pos_l_,
      transpose_spec(g, fadj_col_l, fadj_row_l, radj_col_l_, radj_row_l_, n) &&
      IntArray::full(fadj_col, m_of(fadj_row_l), fadj_col_l) *
      IntArray::full(fadj_row, n + 1, fadj_row_l) *
      IntArray::full(radj_col, m_of(fadj_row_l), radj_col_l_) *
      IntArray::full(radj_row, n + 1, radj_row_l_) *
      IntArray::full(pos, n, pos_l_)
*/
{
  /* pass 1: zero the in-degree counters in radj_row[0..n-1] */
  /*@ Inv Assert
      exists rr_m,
        0 <= v && v <= n && 1 <= n && n <= 2147483647 &&
        IntArray::full(fadj_col, m_of(fadj_row_l), fadj_col_l) *
        IntArray::full(fadj_row, n + 1, fadj_row_l) *
        IntArray::full(radj_col, m_of(fadj_row_l), radj_col_l) *
        IntArray::full(radj_row, n + 1, rr_m) *
        IntArray::full(pos, n, pos_l)
  */
  for (int v = 0; v < n; v++) {
    /*@ Given rr_m */
    radj_row[v] = 0;
  }
  /* pass 2: count in-degrees: for each forward edge (u, v=fadj_col[j]),
     increment radj_row[v] */
  /*@ Inv Assert
      exists rr_m,
        m == m_of(fadj_row_l) && 0 <= j && j <= m && 1 <= n && n <= 2147483647 &&
        IntArray::full(fadj_col, m_of(fadj_row_l), fadj_col_l) *
        IntArray::full(fadj_row, n + 1, fadj_row_l) *
        IntArray::full(radj_col, m_of(fadj_row_l), radj_col_l) *
        IntArray::full(radj_row, n + 1, rr_m) *
        IntArray::full(pos, n, pos_l)
  */
  for (int j = 0; j < m; j++) {
    /*@ Given rr_m */
    int v = fadj_col[j];
    /*@ Assert
        0 <= j && j < m_of(fadj_row_l) && m == m_of(fadj_row_l) &&
        1 <= n && n <= 2147483647 &&
        0 <= v && v < n && v == Znth(j, fadj_col_l, 0) &&
        IntArray::full(fadj_col, m_of(fadj_row_l), fadj_col_l) *
        IntArray::full(fadj_row, n + 1, fadj_row_l) *
        IntArray::full(radj_col, m_of(fadj_row_l), radj_col_l) *
        IntArray::full(radj_row, n + 1, rr_m) *
        IntArray::full(pos, n, pos_l)
    */
    radj_row[v] = radj_row[v] + 1;
  }
  /* pass 3: prefix-sum: radj_row[v] = offset of v's in-bucket;
     radj_row[n] = total edge count = m.  Copy offsets into pos. */
  int sum = 0;
  /*@ Inv Assert
      exists rr_m pos_m,
        0 <= v && v <= n && 1 <= n && n <= 2147483647 && 0 <= sum &&
        IntArray::full(fadj_col, m_of(fadj_row_l), fadj_col_l) *
        IntArray::full(fadj_row, n + 1, fadj_row_l) *
        IntArray::full(radj_col, m_of(fadj_row_l), radj_col_l) *
        IntArray::full(radj_row, n + 1, rr_m) *
        IntArray::full(pos, n, pos_m)
  */
  for (int v = 0; v < n; v++) {
    /*@ Given rr_m pos_m */
    int deg = radj_row[v];
    radj_row[v] = sum;
    pos[v] = sum;
    sum = sum + deg;
  }
  radj_row[n] = sum;
  /* pass 4: scatter.  Outer loop over source vertex u; inner loop over
     u's forward neighbour range [fadj_row[u], fadj_row[u+1]).  For each
     edge (u,v): radj_col[pos[v]] := u; pos[v]++.  radj_row is untouched
     and stays in offset form. */
  /*@ Inv Assert
      exists rc_m rr_m pos_m,
        0 <= u && u <= n && 1 <= n && n <= 2147483647 &&
        store(&sum, int, m) &&
        IntArray::full(fadj_col, m_of(fadj_row_l), fadj_col_l) *
        IntArray::full(fadj_row, n + 1, fadj_row_l) *
        IntArray::full(radj_col, m_of(fadj_row_l), rc_m) *
        IntArray::full(radj_row, n + 1, rr_m) *
        IntArray::full(pos, n, pos_m)
  */
  for (int u = 0; u < n; u++) {
    /*@ Given rc_m rr_m pos_m */
    int lo = fadj_row[u];
    int hi = fadj_row[u + 1];
    int j = lo;
    /*@ Inv Assert
        exists rc_m rr_m pos_m,
          0 <= u && u < n && 1 <= n && n <= 2147483647 &&
          lo == csr_lo(u, fadj_row_l) && hi == csr_hi(u, fadj_row_l) &&
          0 <= lo && lo <= j && j <= hi && hi <= m_of(fadj_row_l) &&
          IntArray::full(fadj_col, m_of(fadj_row_l), fadj_col_l) *
          IntArray::full(fadj_row, n + 1, fadj_row_l) *
          IntArray::full(radj_col, m_of(fadj_row_l), rc_m) *
          IntArray::full(radj_row, n + 1, rr_m) *
          IntArray::full(pos, n, pos_m)
    */
    while (j < hi) {
      int v = fadj_col[j];
      /*@ Assert
          0 <= j && j < m_of(fadj_row_l) &&
          0 <= v && v < n && v == Znth(j, fadj_col_l, 0) &&
          0 <= u && u < n && 1 <= n && n <= 2147483647 &&
          IntArray::full(fadj_col, m_of(fadj_row_l), fadj_col_l) *
          IntArray::full(fadj_row, n + 1, fadj_row_l) *
          IntArray::full(radj_col, m_of(fadj_row_l), rc_m) *
          IntArray::full(radj_row, n + 1, rr_m) *
          IntArray::full(pos, n, pos_m)
      */
      int p = pos[v];
      /*@ Assert
          0 <= j && j < hi && 0 <= p && p < m_of(fadj_row_l) &&
          0 <= v && v < n && 0 <= u && u < n && 1 <= n && n <= 2147483647 &&
          IntArray::full(fadj_col, m_of(fadj_row_l), fadj_col_l) *
          IntArray::full(fadj_row, n + 1, fadj_row_l) *
          IntArray::full(radj_col, m_of(fadj_row_l), rc_m) *
          IntArray::full(radj_row, n + 1, rr_m) *
          IntArray::full(pos, n, pos_m)
      */
      radj_col[p] = u;
      pos[v] = p + 1;
      j = j + 1;
    }
  }
}

/* ==================================================================== */
/* sort_by_fin: arrange vertex indices into `order` so that finish     */
/*   values are NON-INCREASING along the order.  order[] is first      */
/*   initialised to the identity permutation [0,1,...,n-1], then an    */
/*   insertion sort keyed on fin[order[k]] rearranges it into          */
/*   non-increasing finish order (ties kept in original relative order */
/*   — stable, matching the design doc's non-strict requirement).     */
/*   Postcondition: order_spec(fin_l, order_l, n).                     */
/*   Mirrors sortArray.c's Permutation + sort invariant, adapted to    */
/*   a non-increasing key over the indirect array fin[order[.]].       */
/*   high_level_spec <= low_level_spec (no monad; pure arrays).        */
/* ==================================================================== */
void sort_by_fin(int *order, int *fin, int n)
/*@ high_level_spec <= low_level_spec
    With fin_l order_l
    Require
      1 <= n && n <= 2147483647 &&
      IntArray::full(fin, n, fin_l) *
      IntArray::full(order, n, order_l)
    Ensure
      exists order_l_,
      order_spec(fin_l, order_l_, n) &&
      IntArray::full(fin, n, fin_l) *
      IntArray::full(order, n, order_l_)
*/;
void sort_by_fin(int *order, int *fin, int n)
/*@ low_level_spec
    With fin_l order_l
    Require
      1 <= n && n <= 2147483647 &&
      IntArray::full(fin, n, fin_l) *
      IntArray::full(order, n, order_l)
    Ensure
      exists order_l_,
      order_spec(fin_l, order_l_, n) &&
      IntArray::full(fin, n, fin_l) *
      IntArray::full(order, n, order_l_)
*/
{
  /* initialise order[k] = k  (identity permutation of [0..n)) */
  /*@ Inv Assert
      exists om,
        1 <= n && n <= 2147483647 && 0 <= k && k <= n &&
        IntArray::full(fin, n, fin_l) *
        IntArray::full(order, n, om)
  */
  for (int k = 0; k < n; k++) {
    /*@ Given om */
    order[k] = k;
  }
  /* insertion sort: for i = 1 .. n-1, take key = order[i], shift the
     prefix order[0..i-1] right while fin[order[j]] < fin[key], then
     drop key at order[j+1].  This yields NON-INCREASING finish.

     RESOURCE-RECLAIM NOTE (validated on isolated probe + sortArray.c/
     sll.c patterns): wj/fw are declared in the FUNCTION scope (before
     the outer for) and their store(&wj,_) * store(&fw,_) facts are
     carried in BOTH the outer-for Inv and the inner-while Inv, so they
     persist across every back-edge and QCP can reclaim them at function
     exit.  Declaring them inside the loop body (r1) left their scalar
     permissions un-absorbed at the break / back-edge, causing
     "Fail to Remove Memory Permission of fw".  Every Assert that crosses
     a live local carries store(&x, xval) for key/fkey/j/wj/fw. */
  int wj = 0;
  int fw = 0;
  /*@ Inv Assert
      exists om wjv fwv,
        1 <= n && n <= 2147483647 && 1 <= i && i <= n &&
        store(&wj, wjv) *
        store(&fw, fwv) *
        IntArray::full(fin, n, fin_l) *
        IntArray::full(order, n, om)
  */
  for (int i = 1; i < n; i++) {
    /*@ Given om wjv fwv */
    int key = order[i];
    /*@ Assert
        exists keyv,
        1 <= n && n <= 2147483647 && 1 <= i && i < n &&
        0 <= keyv && keyv < n && keyv == Znth(i, om, 0) &&
        store(&key, keyv) *
        store(&wj, wjv) *
        store(&fw, fwv) *
        IntArray::full(fin, n, fin_l) *
        IntArray::full(order, n, om)
    */
    /*@ Given keyv */
    int fkey = fin[key];
    /*@ Assert
        exists fkeyv,
        1 <= n && n <= 2147483647 && 1 <= i && i < n &&
        0 <= keyv && keyv < n && keyv == Znth(i, om, 0) &&
        0 <= fkeyv && fkeyv <= 2147483647 && fkeyv == Znth(keyv, fin_l, 0) &&
        store(&key, keyv) *
        store(&fkey, fkeyv) *
        store(&wj, wjv) *
        store(&fw, fwv) *
        IntArray::full(fin, n, fin_l) *
        IntArray::full(order, n, om)
    */
    /*@ Given fkeyv */
    int j = i - 1;
    /*@ Assert
        exists jv,
        1 <= n && n <= 2147483647 && 1 <= i && i < n &&
        0 <= keyv && keyv < n && keyv == Znth(i, om, 0) &&
        0 <= fkeyv && fkeyv <= 2147483647 && fkeyv == Znth(keyv, fin_l, 0) &&
        -1 <= jv && jv < i && jv == i - 1 &&
        store(&key, keyv) *
        store(&fkey, fkeyv) *
        store(&j, jv) *
        store(&wj, wjv) *
        store(&fw, fwv) *
        IntArray::full(fin, n, fin_l) *
        IntArray::full(order, n, om)
    */
    /*@ Given jv */
    /*@ Inv Assert
        exists om2 wjv2 fwv2,
          1 <= n && n <= 2147483647 && 1 <= i && i < n &&
          -1 <= jv && jv < i &&
          0 <= keyv && keyv < n && keyv == Znth(i, om, 0) &&
          0 <= fkeyv && fkeyv <= 2147483647 && fkeyv == Znth(keyv, fin_l, 0) &&
          store(&key, keyv) *
          store(&fkey, fkeyv) *
          store(&j, jv) *
          store(&wj, wjv2) *
          store(&fw, fwv2) *
          IntArray::full(fin, n, fin_l) *
          IntArray::full(order, n, om2)
    */
    while (j >= 0) {
      /*@ Given om2 wjv2 fwv2 */
      wj = order[j];
      /*@ Assert
          exists wjv3,
          1 <= n && n <= 2147483647 && 0 <= jv && jv < i &&
          0 <= keyv && keyv < n && 0 <= fkeyv && fkeyv <= 2147483647 &&
          0 <= wjv3 && wjv3 < n && wjv3 == Znth(jv, om2, 0) &&
          store(&key, keyv) *
          store(&fkey, fkeyv) *
          store(&j, jv) *
          store(&wj, wjv3) *
          store(&fw, fwv2) *
          IntArray::full(fin, n, fin_l) *
          IntArray::full(order, n, om2)
      */
      /*@ Given wjv3 */
      fw = fin[wj];
      /*@ Assert
          exists fwv3,
          1 <= n && n <= 2147483647 && 0 <= jv && jv < i &&
          0 <= keyv && keyv < n && 0 <= fkeyv && fkeyv <= 2147483647 &&
          0 <= wjv3 && wjv3 < n && wjv3 == Znth(jv, om2, 0) &&
          0 <= fwv3 && fwv3 <= 2147483647 && fwv3 == Znth(wjv3, fin_l, 0) &&
          store(&key, keyv) *
          store(&fkey, fkeyv) *
          store(&j, jv) *
          store(&wj, wjv3) *
          store(&fw, fwv3) *
          IntArray::full(fin, n, fin_l) *
          IntArray::full(order, n, om2)
      */
      /*@ Given fwv3 */
      if (fw < fkey) {
        /*@ Assert
            1 <= n && n <= 2147483647 && 0 <= jv && jv < i &&
            0 <= keyv && keyv < n && 0 <= fkeyv && fkeyv <= 2147483647 &&
            0 <= wjv3 && wjv3 < n && wjv3 == Znth(jv, om2, 0) &&
            0 <= jv + 1 && jv + 1 < n &&
            store(&key, keyv) *
            store(&fkey, fkeyv) *
            store(&j, jv) *
            store(&wj, wjv3) *
            store(&fw, fwv3) *
            IntArray::full(fin, n, fin_l) *
            IntArray::full(order, n, om2)
        */
        order[j + 1] = wj;
        /*@ Assert
            exists om2b,
            1 <= n && n <= 2147483647 && 0 <= jv && jv < i &&
            0 <= keyv && keyv < n && keyv == Znth(i, om, 0) &&
            0 <= fkeyv && fkeyv <= 2147483647 && fkeyv == Znth(keyv, fin_l, 0) &&
            store(&key, keyv) *
            store(&fkey, fkeyv) *
            store(&j, jv) *
            store(&wj, wjv3) *
            store(&fw, fwv3) *
            IntArray::full(fin, n, fin_l) *
            IntArray::full(order, n, om2b)
        */
        /*@ Given om2b */
        j = j - 1;
      } else {
        /*@ Assert
            1 <= n && n <= 2147483647 && 0 <= jv && jv < i &&
            0 <= keyv && keyv < n && keyv == Znth(i, om, 0) &&
            0 <= fkeyv && fkeyv <= 2147483647 && fkeyv == Znth(keyv, fin_l, 0) &&
            store(&key, keyv) *
            store(&fkey, fkeyv) *
            store(&j, jv) *
            store(&wj, wjv3) *
            store(&fw, fwv3) *
            IntArray::full(fin, n, fin_l) *
            IntArray::full(order, n, om2)
        */
        break;
      }
    }
    /*@ Assert
        exists om2 jf wjf fwf,
        1 <= n && n <= 2147483647 && 1 <= i && i < n &&
        -1 <= jf && jf < i && 0 <= jf + 1 && jf + 1 < n &&
        0 <= keyv && keyv < n && keyv == Znth(i, om, 0) &&
        0 <= fkeyv && fkeyv <= 2147483647 && fkeyv == Znth(keyv, fin_l, 0) &&
        store(&key, keyv) *
        store(&fkey, fkeyv) *
        store(&j, jf) *
        store(&wj, wjf) *
        store(&fw, fwf) *
        IntArray::full(fin, n, fin_l) *
        IntArray::full(order, n, om2)
    */
    order[j + 1] = key;
  }
}

/* ==================================================================== */
/* kosaraju: top-level SCC driver (direct-proof external interface,    */
/*   mirroring kmp_rel.c:main).  Takes the forward CSR + an output sid */
/*   buffer; mallocs all working arrays internally and frees them      */
/*   before return, so the external spec mentions only fadj_* and sid. */
/*   Composes: transpose -> phase-1 dfs1 sweep -> sort_by_fin ->       */
/*   phase-2 dfs2 sweep over the sorted order.                         */
/*   Ensure: the output sid labels vertices so that                    */
/*     sid[u] = sid[v]  <=>  mutually_reachable g u v   (same SCC).    */
/* ==================================================================== */
void kosaraju(int n, int *fadj_col, int *fadj_row, int *sid)
/*@ high_level_spec
    With g fadj_col_l fadj_row_l sid_l
    Require
      1 <= n && n <= 2147483647 &&
      csr2_faithful(g, fadj_col_l, fadj_row_l) &&
      AdjGraphValid(g) &&
      adj_verts(g) == n &&
      IntArray::full(fadj_col, m_of(fadj_row_l), fadj_col_l) *
      IntArray::full(fadj_row, n + 1, fadj_row_l) *
      IntArray::full(sid, n, sid_l)
    Ensure
      exists sid_l_,
      (forall (u: Z), (0 <= u && u < n) =>
         (forall (v: Z), (0 <= v && v < n) =>
            ((Znth(u, sid_l_, 0) == Znth(v, sid_l_, 0) => mutually_reachable(g, u, v))
             && (mutually_reachable(g, u, v) => Znth(u, sid_l_, 0) == Znth(v, sid_l_, 0))))) &&
      IntArray::full(fadj_col, m_of(fadj_row_l), fadj_col_l) *
      IntArray::full(fadj_row, n + 1, fadj_row_l) *
      IntArray::full(sid, n, sid_l_)
*/
{
  int m = fadj_row[n];
  int *radj_col = malloc_int_array(m);
  int *radj_row = malloc_int_array(n + 1);
  int *pos = malloc_int_array(n);
  int *vis1 = malloc_int_array(n);
  int *fin = malloc_int_array(n);
  int *vis2 = malloc_int_array(n);
  int *order = malloc_int_array(n);
  int *timer_p = malloc_int_array(1);

  /* capture the arbitrary contents returned by malloc for the working
     arrays that transpose will overwrite. */
  /*@ Assert
      exists radj_col_l0 radj_row_l0 pos_l0 vis1_l0 fin_l0 vis2_l0 order_l0,
        n == n@pre && m == m_of(fadj_row_l) &&
        1 <= n && n <= 2147483647 &&
        IntArray::full(fadj_col, m_of(fadj_row_l), fadj_col_l) *
        IntArray::full(fadj_row, n + 1, fadj_row_l) *
        IntArray::full(sid, n, sid_l) *
        IntArray::full(radj_col, m_of(fadj_row_l), radj_col_l0) *
        IntArray::full(radj_row, n + 1, radj_row_l0) *
        IntArray::full(pos, n, pos_l0) *
        IntArray::full(vis1, n, vis1_l0) *
        IntArray::full(fin, n, fin_l0) *
        IntArray::full(vis2, n, vis2_l0) *
        IntArray::full(order, n, order_l0) *
        IntArray::full(timer_p, 1, cons(0, nil))
  */
  /*@ Given radj_col_l0 radj_row_l0 pos_l0 vis1_l0 fin_l0 vis2_l0 order_l0 */

  /* initialise vis1, vis2, fin, timer_p to zero */
  /*@ Inv Assert
      exists radj_col_l0 radj_row_l0 pos_l0 order_l0 vm fm vm2,
        n == n@pre && m == m_of(fadj_row_l) &&
        fadj_col == fadj_col@pre && fadj_row == fadj_row@pre && sid == sid@pre &&
        1 <= n && n <= 2147483647 && 0 <= u && u <= n &&
        IntArray::full(fadj_col, m_of(fadj_row_l), fadj_col_l) *
        IntArray::full(fadj_row, n + 1, fadj_row_l) *
        IntArray::full(sid, n, sid_l) *
        IntArray::full(radj_col, m_of(fadj_row_l), radj_col_l0) *
        IntArray::full(radj_row, n + 1, radj_row_l0) *
        IntArray::full(pos, n, pos_l0) *
        IntArray::full(vis1, n, vm) *
        IntArray::full(fin, n, fm) *
        IntArray::full(vis2, n, vm2) *
        IntArray::full(order, n, order_l0) *
        IntArray::full(timer_p, 1, cons(0, nil))
  */
  for (int u = 0; u < n; u++) {
    /*@ Given vm fm vm2 */
    vis1[u] = 0;
    vis2[u] = 0;
    fin[u] = 0;
  }
  timer_p[0] = 0;

  /* capture the zeroed working arrays (vis1_zero/fin_zero/vis2_zero). */
  /*@ Assert
      exists vis1_zero fin_zero vis2_zero,
        n == n@pre && m == m_of(fadj_row_l) &&
        1 <= n && n <= 2147483647 &&
        IntArray::full(fadj_col, m_of(fadj_row_l), fadj_col_l) *
        IntArray::full(fadj_row, n + 1, fadj_row_l) *
        IntArray::full(sid, n, sid_l) *
        IntArray::full(radj_col, m_of(fadj_row_l), radj_col_l0) *
        IntArray::full(radj_row, n + 1, radj_row_l0) *
        IntArray::full(pos, n, pos_l0) *
        IntArray::full(vis1, n, vis1_zero) *
        IntArray::full(fin, n, fin_zero) *
        IntArray::full(vis2, n, vis2_zero) *
        IntArray::full(order, n, order_l0) *
        IntArray::full(timer_p, 1, cons(0, nil))
  */
  /*@ Given vis1_zero fin_zero vis2_zero */

  /* step C: build the reverse CSR from the forward CSR.  The working
     arrays' pre-call contents (radj_col_l0/radj_row_l0/pos_l0) are
     arbitrary; transpose overwrites them. */
  /*@ Assert
      n == n@pre && m == m_of(fadj_row_l) &&
      1 <= n && n <= 2147483647 &&
      csr2_faithful(g, fadj_col_l, fadj_row_l) &&
      AdjGraphValid(g) && adj_verts(g) == n &&
      IntArray::full(fadj_col, m_of(fadj_row_l), fadj_col_l) *
      IntArray::full(fadj_row, n + 1, fadj_row_l) *
      IntArray::full(sid, n, sid_l) *
      IntArray::full(radj_col, m_of(fadj_row_l), radj_col_l0) *
      IntArray::full(radj_row, n + 1, radj_row_l0) *
      IntArray::full(pos, n, pos_l0) *
      IntArray::full(vis1, n, vis1_zero) *
      IntArray::full(fin, n, fin_zero) *
      IntArray::full(vis2, n, vis2_zero) *
      IntArray::full(order, n, order_l0) *
      IntArray::full(timer_p, 1, cons(0, nil))
  */
  transpose(n, m, fadj_col, fadj_row, radj_col, radj_row, pos)
      /*@ where(high_level_spec)
            g = g,
            fadj_col_l = fadj_col_l, fadj_row_l = fadj_row_l,
            radj_col_l = radj_col_l0, radj_row_l = radj_row_l0,
            pos_l = pos_l0 */;
  /*@ Assert
      exists radj_col_l radj_row_l pos_l,
        transpose_spec(g, fadj_col_l, fadj_row_l, radj_col_l, radj_row_l, n) &&
        n == n@pre && m == m_of(fadj_row_l) &&
        1 <= n && n <= 2147483647 && adj_verts(g) == n &&
        IntArray::full(fadj_col, m_of(fadj_row_l), fadj_col_l) *
        IntArray::full(fadj_row, n + 1, fadj_row_l) *
        IntArray::full(sid, n, sid_l) *
        IntArray::full(radj_col, m_of(radj_row_l), radj_col_l) *
        IntArray::full(radj_row, n + 1, radj_row_l) *
        IntArray::full(pos, n, pos_l) *
        IntArray::full(vis1, n, vis1_zero) *
        IntArray::full(fin, n, fin_zero) *
        IntArray::full(vis2, n, vis2_zero) *
        IntArray::full(order, n, order_l0) *
        IntArray::full(timer_p, 1, cons(0, nil))
  */
  /*@ Given radj_col_l radj_row_l pos_l */

  /* step A (phase 1): for each unvisited1 vertex, run dfs1 on the
     reverse graph to assign finish times.  Loop invariant threads the
     visited1/fin/timer arrays; each dfs1 call refines them. */
  /*@ Inv Assert
      exists vis1_m fin_m timer_m,
        n == n@pre && m == m_of(fadj_row_l) &&
        fadj_col == fadj_col@pre && fadj_row == fadj_row@pre && sid == sid@pre &&
        1 <= n && n <= 2147483647 && 0 <= u && u <= n &&
        IntArray::full(fadj_col, m_of(fadj_row_l), fadj_col_l) *
        IntArray::full(fadj_row, n + 1, fadj_row_l) *
        IntArray::full(sid, n, sid_l) *
        IntArray::full(radj_col, m_of(radj_row_l), radj_col_l) *
        IntArray::full(radj_row, n + 1, radj_row_l) *
        IntArray::full(vis1, n, vis1_m) *
        IntArray::full(fin, n, fin_m) *
        IntArray::full(vis2, n, vis2_zero) *
        IntArray::full(order, n, order_l0) *
        IntArray::full(timer_p, 1, cons(timer_m, nil))
  */
  for (int u = 0; u < n; u++) {
    /*@ Given vis1_m fin_m timer_m */
    if (vis1[u] == 0) {
      /*@ Assert
          csr_wf1(g, radj_col_l, radj_row_l, vis1_m, fin_m) &&
          csr1_faithful(g, radj_col_l, radj_row_l) &&
          adj_verts(g) == n &&
          0 <= u && u < n && n <= 2147483647 &&
          Znth(u, vis1_m, 0) == 0 &&
          0 <= timer_m &&
          IntArray::full(radj_col, m_of(radj_row_l), radj_col_l) *
          IntArray::full(radj_row, n + 1, radj_row_l) *
          IntArray::full(vis1, n, vis1_m) *
          IntArray::full(fin, n, fin_m) *
          IntArray::full(timer_p, 1, cons(timer_m, nil))
      */
      dfs1(u, n, radj_col, radj_row, vis1, fin, timer_p)
          /*@ where(high_level_spec)
                g = g,
                radj_col_l = radj_col_l, radj_row_l = radj_row_l,
                vis1_l = vis1_m, fin_l = fin_m, timer_v = timer_m */;
      /*@ Assert
          exists vis1_m_ fin_m_ timer_m_,
            dfs1_high_level_post(g, radj_col_l, radj_row_l,
                                    vis1_m, fin_m, vis1_m_, fin_m_,
                                    u, timer_m, timer_m_, n) &&
            adj_verts(g) == n &&
            IntArray::full(radj_col, m_of(radj_row_l), radj_col_l) *
            IntArray::full(radj_row, n + 1, radj_row_l) *
            IntArray::full(vis1, n, vis1_m_) *
            IntArray::full(fin, n, fin_m_) *
            IntArray::full(timer_p, 1, cons(timer_m_, nil))
      */
      /*@ Given vis1_m_ fin_m_ timer_m_ */
    }
  }

  /* step D: sort vertex indices into non-increasing finish order.
     fin now holds the phase-1 finish times (loop-final fin_m). */
  /*@ Assert
      exists vis1_m fin_m timer_m,
        n == n@pre && m == m_of(fadj_row_l) && 1 <= n && n <= 2147483647 &&
        IntArray::full(fadj_col, m_of(fadj_row_l), fadj_col_l) *
        IntArray::full(fadj_row, n + 1, fadj_row_l) *
        IntArray::full(sid, n, sid_l) *
        IntArray::full(radj_col, m_of(radj_row_l), radj_col_l) *
        IntArray::full(radj_row, n + 1, radj_row_l) *
        IntArray::full(pos, n, pos_l) *
        IntArray::full(vis1, n, vis1_m) *
        IntArray::full(fin, n, fin_m) *
        IntArray::full(vis2, n, vis2_zero) *
        IntArray::full(order, n, order_l0) *
        IntArray::full(timer_p, 1, cons(timer_m, nil))
  */
  /*@ Given vis1_m fin_m timer_m */
  sort_by_fin(order, fin, n)
      /*@ where(high_level_spec)
            fin_l = fin_m, order_l = order_l0 */;
  /*@ Assert
      exists order_l,
        order_spec(fin_m, order_l, n) &&
        n == n@pre && m == m_of(fadj_row_l) && 1 <= n && n <= 2147483647 &&
        IntArray::full(fadj_col, m_of(fadj_row_l), fadj_col_l) *
        IntArray::full(fadj_row, n + 1, fadj_row_l) *
        IntArray::full(sid, n, sid_l) *
        IntArray::full(radj_col, m_of(radj_row_l), radj_col_l) *
        IntArray::full(radj_row, n + 1, radj_row_l) *
        IntArray::full(pos, n, pos_l) *
        IntArray::full(vis1, n, vis1_m) *
        IntArray::full(fin, n, fin_m) *
        IntArray::full(vis2, n, vis2_zero) *
        IntArray::full(order, n, order_l) *
        IntArray::full(timer_p, 1, cons(timer_m, nil))
  */
  /*@ Given order_l */

  /* step B (phase 2): sweep the sorted order; for each unvisited2 root,
     run dfs2(root, root, ...) to label its whole SCC. */
  /*@ Inv Assert
      exists vis2_m sid_m,
        n == n@pre && m == m_of(fadj_row_l) &&
        fadj_col == fadj_col@pre && fadj_row == fadj_row@pre &&
        1 <= n && n <= 2147483647 && 0 <= k && k <= n &&
        IntArray::full(fadj_col, m_of(fadj_row_l), fadj_col_l) *
        IntArray::full(fadj_row, n + 1, fadj_row_l) *
        IntArray::full(sid, n, sid_m) *
        IntArray::full(vis2, n, vis2_m) *
        IntArray::full(fin, n, fin_m) *
        IntArray::full(order, n, order_l) *
        IntArray::full(radj_col, m_of(radj_row_l), radj_col_l) *
        IntArray::full(radj_row, n + 1, radj_row_l) *
        IntArray::full(pos, n, pos_l) *
        IntArray::full(vis1, n, vis1_m) *
        IntArray::full(timer_p, 1, cons(timer_m, nil))
  */
  for (int k = 0; k < n; k++) {
    /*@ Given vis2_m sid_m */
    int root = order[k];
    /*@ Assert
        1 <= n && n <= 2147483647 &&
        0 <= root && root < n && root == Znth(k, order_l, 0) &&
        IntArray::full(fadj_col, m_of(fadj_row_l), fadj_col_l) *
        IntArray::full(fadj_row, n + 1, fadj_row_l) *
        IntArray::full(sid, n, sid_m) *
        IntArray::full(vis2, n, vis2_m) *
        IntArray::full(fin, n, fin_m) *
        IntArray::full(order, n, order_l) *
        IntArray::full(radj_col, m_of(radj_row_l), radj_col_l) *
        IntArray::full(radj_row, n + 1, radj_row_l) *
        IntArray::full(pos, n, pos_l) *
        IntArray::full(vis1, n, vis1_m) *
        IntArray::full(timer_p, 1, cons(timer_m, nil))
    */
    if (vis2[root] == 0) {
      /* pre-mark #1: vis2[root] = 1.  dfs2's high_level_spec Require is
         Znth(root, vis2_l, 0) != 0, so the root must be marked visited2
         BEFORE the dfs2 call.  Mirror transpose's write-before pattern:
         ONE pre-write Assert exposing the current Inv list value; NO
         post-write Assert (the back-edge Inv rebinds the list). */
      /*@ Assert
          1 <= n && n <= 2147483647 &&
          0 <= root && root < n && root == Znth(k, order_l, 0) &&
          Znth(root, vis2_m, 0) == 0 &&
          IntArray::full(fadj_col, m_of(fadj_row_l), fadj_col_l) *
          IntArray::full(fadj_row, n + 1, fadj_row_l) *
          IntArray::full(sid, n, sid_m) *
          IntArray::full(vis2, n, vis2_m) *
          IntArray::full(fin, n, fin_m) *
          IntArray::full(order, n, order_l) *
          IntArray::full(radj_col, m_of(radj_row_l), radj_col_l) *
          IntArray::full(radj_row, n + 1, radj_row_l) *
          IntArray::full(pos, n, pos_l) *
          IntArray::full(vis1, n, vis1_m) *
          IntArray::full(timer_p, 1, cons(timer_m, nil))
      */
      vis2[root] = 1;
      /* pre-mark #2: sid[root] = root.  dfs2 reads sid[root] and labels
         every vertex in root's SCC with sid[root]; setting sid[root]=root
         BEFORE the call makes the SCC representative equal to root itself
         (standard Kosaraju structure).  Same write-before pattern. */
      /*@ Assert
          exists vis2_m1,
            1 <= n && n <= 2147483647 &&
            0 <= root && root < n && root == Znth(k, order_l, 0) &&
            Znth(root, vis2_m1, 0) == 1 &&
            IntArray::full(fadj_col, m_of(fadj_row_l), fadj_col_l) *
            IntArray::full(fadj_row, n + 1, fadj_row_l) *
            IntArray::full(sid, n, sid_m) *
            IntArray::full(vis2, n, vis2_m1) *
            IntArray::full(fin, n, fin_m) *
            IntArray::full(order, n, order_l) *
            IntArray::full(radj_col, m_of(radj_row_l), radj_col_l) *
            IntArray::full(radj_row, n + 1, radj_row_l) *
            IntArray::full(pos, n, pos_l) *
            IntArray::full(vis1, n, vis1_m) *
            IntArray::full(timer_p, 1, cons(timer_m, nil))
      */
      /*@ Given vis2_m1 */
      sid[root] = root;
      /* dfs2 pre-call Assert: expose the POST-write vis2/sid state (root
         now visited2 and sid[root]=root), satisfying dfs2's Require
         Znth(root, vis2_l, 0) != 0.  The logical preconditions
         csr_wf2 / csr2_faithful frame the call.  root == u here
         (dfs2(root, root, ...)), so the call labels root's whole SCC. */
      /*@ Assert
          exists vis2_m1 sid_m1,
            csr_wf2(g, fadj_col_l, fadj_row_l, vis2_m1, sid_m1) &&
            csr2_faithful(g, fadj_col_l, fadj_row_l) &&
            adj_verts(g) == n &&
            1 <= n && n <= 2147483647 &&
            0 <= root && root < n && root == Znth(k, order_l, 0) &&
            Znth(root, vis2_m1, 0) != 0 &&
            Znth(root, sid_m1, 0) == root &&
            IntArray::full(fadj_col, m_of(fadj_row_l), fadj_col_l) *
            IntArray::full(fadj_row, n + 1, fadj_row_l) *
            IntArray::full(vis2, n, vis2_m1) *
            IntArray::full(sid, n, sid_m1) *
            IntArray::full(fin, n, fin_m) *
            IntArray::full(order, n, order_l) *
            IntArray::full(radj_col, m_of(radj_row_l), radj_col_l) *
            IntArray::full(radj_row, n + 1, radj_row_l) *
            IntArray::full(pos, n, pos_l) *
            IntArray::full(vis1, n, vis1_m) *
            IntArray::full(timer_p, 1, cons(timer_m, nil))
      */
      /*@ Given sid_m1 */
      dfs2(root, root, n, fadj_col, fadj_row, vis2, sid)
          /*@ where(high_level_spec)
                g = g,
                fadj_col_l = fadj_col_l, fadj_row_l = fadj_row_l,
                vis2_l = vis2_m1, sid_l = sid_m1 */;
      /* post-call Assert: capture dfs2's high_level post into fresh
         existentials vis2_m_ sid_m_, threading dfs2_high_level_post
         (C1 root visited2 + sid[root]=root unchanged; C2 prior-visited2
         preserved; C3 newly-visited get sid=sid[root]).  The frame arrays
         are untouched by dfs2. */
      /*@ Assert
          exists vis2_m_ sid_m_,
            dfs2_high_level_post(g, fadj_col_l, fadj_row_l,
                                    vis2_m1, sid_m1, vis2_m_, sid_m_,
                                    root, root, n) &&
            adj_verts(g) == n &&
            1 <= n && n <= 2147483647 &&
            0 <= root && root < n && root == Znth(k, order_l, 0) &&
            IntArray::full(fadj_col, m_of(fadj_row_l), fadj_col_l) *
            IntArray::full(fadj_row, n + 1, fadj_row_l) *
            IntArray::full(vis2, n, vis2_m_) *
            IntArray::full(sid, n, sid_m_) *
            IntArray::full(fin, n, fin_m) *
            IntArray::full(order, n, order_l) *
            IntArray::full(radj_col, m_of(radj_row_l), radj_col_l) *
            IntArray::full(radj_row, n + 1, radj_row_l) *
            IntArray::full(pos, n, pos_l) *
            IntArray::full(vis1, n, vis1_m) *
            IntArray::full(timer_p, 1, cons(timer_m, nil))
      */
      /*@ Given vis2_m_ sid_m_ */
    }
  }

  /* post-phase-2: re-expose all working arrays with their lengths in the
     form free_int_array expects (radj_col length = m, others length n). */
  /*@ Assert
      exists sid_m vis2_m,
        1 <= n && n <= 2147483647 && m == m_of(fadj_row_l) && m == m_of(radj_row_l) &&
        IntArray::full(fadj_col, m_of(fadj_row_l), fadj_col_l) *
        IntArray::full(fadj_row, n + 1, fadj_row_l) *
        IntArray::full(sid, n, sid_m) *
        IntArray::full(radj_col, m, radj_col_l) *
        IntArray::full(radj_row, n + 1, radj_row_l) *
        IntArray::full(pos, n, pos_l) *
        IntArray::full(vis1, n, vis1_m) *
        IntArray::full(fin, n, fin_m) *
        IntArray::full(vis2, n, vis2_m) *
        IntArray::full(order, n, order_l) *
        IntArray::full(timer_p, 1, cons(timer_m, nil))
  */
  /*@ Given sid_m vis2_m */

  /* free all working arrays.  The final sid array carries the SCC
     labeling (sid_m final); the external Ensure's sid_l_ is sid_m. */
  free_int_array(radj_col) /*@ where n = m, l = radj_col_l */;
  free_int_array(radj_row) /*@ where n = n + 1, l = radj_row_l */;
  free_int_array(pos)      /*@ where n = n, l = pos_l */;
  free_int_array(vis1)     /*@ where n = n, l = vis1_m */;
  free_int_array(fin)      /*@ where n = n, l = fin_m */;
  free_int_array(vis2)     /*@ where n = n, l = vis2_m */;
  free_int_array(order)    /*@ where n = n, l = order_l */;
  free_int_array(timer_p)  /*@ where n = 1, l = cons(timer_m, nil) */;
}
