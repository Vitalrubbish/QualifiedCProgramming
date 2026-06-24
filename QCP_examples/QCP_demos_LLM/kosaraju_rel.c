#include "safeexec_def.h"
#include "verification_stdlib.h"
#include "int_array_def.h"
#include "sll_ptr_array_def.h"

/*@ Import Coq Require Import SimpleC.EE.QCP_demos_LLM.kosaraju_rel_lib */

/*@ Extern Coq (KSt :: *) (AdjGraph :: *) */
/*@ Extern Coq
               (dfs_finish: Z -> program KSt unit)
               (dfs_finish_from: Z -> list (Z * Z) -> program KSt unit)
               (dfs_finish_after: Z -> list (Z * Z) -> unit -> program KSt unit)
               (dfs1_ret_cont: unit -> program KSt unit)
               (kosaraju_get_visited1_rel: Z -> list Z -> program KSt Z)
               (pre_dfs1: AdjGraph -> list Z -> list Z -> Z -> KSt -> Prop)
               (edges_of: Z -> list Z -> list (Z * Z))
               (nth_def: {A} -> list A -> Z -> A -> A)
               (dfs_scc: Z -> Z -> program KSt unit)
               (dfs_scc_from: Z -> Z -> list (Z * Z) -> program KSt unit)
               (dfs_scc_after: Z -> Z -> list (Z * Z) -> unit -> program KSt unit)
               (dfs2_ret_cont: unit -> program KSt unit)
               (pre_dfs2: AdjGraph -> list Z -> list Z -> KSt -> Prop)
               (kosaraju_finish_monad: program KSt unit)
               (kosaraju_scc_monad: program KSt unit)
               (kosaraju_monad: program KSt unit)
               (kosaraju_finish_from: Z -> program KSt unit)
               (kosaraju_scc_from: Z -> program KSt unit)
               (pre_kosaraju: AdjGraph -> list Z -> list Z -> list Z -> list Z -> Z -> Z -> KSt -> Prop)
               (order_sorted: list Z -> list Z -> Prop)
                */

int kosaraju_num_vertices(int n)
/*@ low_level_spec
    With X
    Require safeExec(ATrue, dfs_finish(0), X) && emp
    Ensure safeExec(ATrue, dfs_finish(0), X) && emp
 */
{
  return n;
}

int kosaraju_get_visited1(int n, int *vis1, int u)
/*@ low_level_spec
    With vis1_l X
    Require safeExec(ATrue, kosaraju_get_visited1_rel(u, vis1_l), X) &&
            0 <= u && u < n && n <= 2147483647 &&
            IntArray::full(vis1, n, vis1_l)
    Ensure safeExec(ATrue, kosaraju_get_visited1_rel(u, vis1_l), X) &&
            __return == Znth(u, vis1_l, 0) &&
            IntArray::full(vis1, n, vis1_l)
 */
{
  return vis1[u];
}

/* dfs1: reverse-graph DFS, refines dfs_finish u.
   Walks radj[u] with a WHILE loop + cursor [cur].  Graph recursion
   dfs1(v) inside the loop uses where(low_level_spec) — the polymorphic
   low_level_spec_aux form crashes symexec (SIGSEGV) at a self-recursive
   call site inside a while loop.  Cursor advance cur = cur->next is a
   plain Inv-preservation VC (Rocq-side), not a recursion prefill. */
void dfs1(int u, int n, struct list **radj, int *vis1, int *fin, int *timer_p)
/*@ low_level_spec
    With g vis1_l fin_l timer_v X radj_rows
    Require
      safeExec(pre_dfs1(g, vis1_l, fin_l, timer_v), dfs_finish(u), X) &&
      0 <= u && u < n && n <= 2147483647 &&
      SllPtrArray::full(radj, n, radj_rows) *
      IntArray::full(vis1, n, vis1_l) *
      IntArray::full(fin, n, fin_l) *
      IntArray::full(timer_p, 1, cons(timer_v, nil))
    Ensure
      exists vis1_l_ fin_l_ timer_v_,
      safeExec(pre_dfs1(g, vis1_l_, fin_l_, timer_v_), return(tt), X) &&
      SllPtrArray::full(radj, n, radj_rows) *
      IntArray::full(vis1, n, vis1_l_) *
      IntArray::full(fin, n, fin_l_) *
      IntArray::full(timer_p, 1, cons(timer_v_, nil))
 */
{
  vis1[u] = 1;

  struct list *cur;
  cur = radj[u];

  /*@ Inv Assert
      exists head processed rem vis1_m fin_m timer_m,
        safeExec(pre_dfs1(g, vis1_m, fin_m, timer_m),
                 dfs_finish_from(u, edges_of(u, processed)), X) &&
        u == u@pre && n == n@pre &&
        radj == radj@pre && vis1 == vis1@pre && fin == fin@pre &&
        timer_p == timer_p@pre &&
        0 <= u && u < n && n <= 2147483647 &&
        SllPtrArray::missing_i(radj, n, u, head, radj_rows) *
        sllseg(head, cur, processed) *
        sll(cur, rem) *
        IntArray::full(vis1, n, vis1_m) *
        IntArray::full(fin, n, fin_m) *
        IntArray::full(timer_p, 1, cons(timer_m, nil))
  */
  while (cur != (void *)0) {
    int v;
    /*@ Given head processed rem vis1_m fin_m timer_m */
    /*@ Assert
        exists vdata rest next_ptr,
          cur != 0 &&
          v == vdata &&
          0 <= v && v < n && n <= 2147483647 &&
          rem == cons(vdata, rest) &&
          safeExec(pre_dfs1(g, vis1_m, fin_m, timer_m),
                   dfs_finish_from(u, edges_of(u, processed)), X) &&
          SllPtrArray::missing_i(radj, n, u, head, radj_rows) *
          sllseg(head, cur, processed) *
          store(&(cur->data), vdata) * store(&(cur->next), next_ptr) *
          sll(next_ptr, rest) *
          IntArray::full(vis1, n, vis1_m) *
          IntArray::full(fin, n, fin_m) *
          IntArray::full(timer_p, 1, cons(timer_m, nil))
    */
    v = cur->data;

    if (vis1[v] == 0) {
      /*@ Assert
          u == u@pre && n == n@pre &&
          radj == radj@pre && vis1 == vis1@pre && fin == fin@pre &&
          timer_p == timer_p@pre &&
          cur != 0 &&
          0 <= u && u < n && 0 <= v && v < n && n <= 2147483647 &&
          Znth(v, vis1_m, 0) == 0 &&
          safeExec(pre_dfs1(g, vis1_m, fin_m, timer_m),
                   dfs_finish(v), X) &&
          SllPtrArray::full(radj, n, radj_rows) *
          IntArray::full(vis1, n, vis1_m) *
          IntArray::full(fin, n, fin_m) *
          IntArray::full(timer_p, 1, cons(timer_m, nil))
      */
      dfs1(v, n, radj, vis1, fin, timer_p)
          /*@ where(low_level_spec)
                g = g,
                vis1_l = vis1_m, fin_l = fin_m, timer_v = timer_m,
                radj_rows = radj_rows,
                X = X */;
    }

    /*@ Assert
        exists vdata_ rest_ next_ptr_ vis1_m_ fin_m_ timer_m_,
          u == u@pre && n == n@pre &&
          radj == radj@pre && vis1 == vis1@pre && fin == fin@pre &&
          timer_p == timer_p@pre &&
          cur != 0 && v == vdata_ &&
          0 <= u && u < n && n <= 2147483647 &&
          rem == cons(vdata_, rest_) &&
          safeExec(pre_dfs1(g, vis1_m_, fin_m_, timer_m_),
                   dfs_finish_from(u, edges_of(u, processed)), X) &&
          SllPtrArray::missing_i(radj, n, u, head, radj_rows) *
          sllseg(head, cur, processed) *
          store(&(cur->data), vdata_) * store(&(cur->next), next_ptr_) *
          sll(next_ptr_, rest_) *
          IntArray::full(vis1, n, vis1_m_) *
          IntArray::full(fin, n, fin_m_) *
          IntArray::full(timer_p, 1, cons(timer_m_, nil))
    */
    cur = cur->next;
  }

  {
    int t0;
    t0 = timer_p[0];
    /*@ Assert
        exists head vis1_m fin_m timer_m fin_m_set timer_m_set,
          u == u@pre && n == n@pre &&
          radj == radj@pre && vis1 == vis1@pre && fin == fin@pre &&
          timer_p == timer_p@pre &&
          t0 == timer_m &&
          0 <= u && u < n && n <= 2147483647 &&
          fin_m_set == replace_Znth(u, timer_m, fin_m) &&
          timer_m_set == timer_m + 1 &&
          safeExec(pre_dfs1(g, vis1_m, fin_m_set, timer_m_set),
                   return(tt), X) &&
          SllPtrArray::missing_i(radj, n, u, head, radj_rows) *
          sll(head, Znth(u, radj_rows, nil)) *
          store(&cur, struct list*, 0) *
          IntArray::full(vis1, n, vis1_m) *
          IntArray::full(fin, n, fin_m_set) *
          IntArray::full(timer_p, 1, cons(timer_m, nil))
    */
    fin[u] = t0;
    timer_p[0] = t0 + 1;
  }
}

/* dfs2: forward-graph DFS, refines DFS_scc root u.
   Walks fadj[u] (forward-adjacency / out-neighbours of u in the original
   graph) with a WHILE loop + cursor [cur].  Graph recursion dfs2(root,v)
   inside the loop uses where(low_level_spec) — the polymorphic
   low_level_spec_aux form crashes symexec (SIGSEGV) at a self-recursive
   call site inside a while loop (same lesson as dfs1).  The same root is
   passed to every recursion so root's scc_id propagates within the SCC.
   Cursor advance cur = cur->next is a plain Inv-preservation VC, not a
   recursion prefill.  Unlike dfs1, dfs2 does NOT record finish times:
   DFS_scc's break branch only breaks (no set_finish / no timer). */
void dfs2(int root, int u, int n, struct list **fadj, int *vis2, int *sid)
/*@ low_level_spec
    With g vis2_l sid_l X fadj_rows
    Require
      safeExec(pre_dfs2(g, vis2_l, sid_l), dfs_scc(root, u), X) &&
      0 <= root && root < n && 0 <= u && u < n && n <= 2147483647 &&
      SllPtrArray::full(fadj, n, fadj_rows) *
      IntArray::full(vis2, n, vis2_l) *
      IntArray::full(sid, n, sid_l)
    Ensure
      exists vis2_l_ sid_l_,
      safeExec(pre_dfs2(g, vis2_l_, sid_l_), return(tt), X) &&
      SllPtrArray::full(fadj, n, fadj_rows) *
      IntArray::full(vis2, n, vis2_l_) *
      IntArray::full(sid, n, sid_l_)
 */
{
  /* visit2 u ;; set_scc_id u root  —  mark visited2[u]=1, propagate
     root's scc_id into u.  sid_l after set_scc_id has
     Znth(u, sid_l, 0) = Znth(root, sid_l, 0). */
  vis2[u] = 1;
  sid[u] = sid[root];

  struct list *cur;
  cur = fadj[u];

  /*@ Inv Assert
      exists head processed rem vis2_m sid_m,
        safeExec(pre_dfs2(g, vis2_m, sid_m),
                 dfs_scc_from(root, u, edges_of(u, processed)), X) &&
        root == root@pre && u == u@pre && n == n@pre &&
        fadj == fadj@pre && vis2 == vis2@pre && sid == sid@pre &&
        0 <= root && root < n && 0 <= u && u < n && n <= 2147483647 &&
        SllPtrArray::missing_i(fadj, n, u, head, fadj_rows) *
        sllseg(head, cur, processed) *
        sll(cur, rem) *
        IntArray::full(vis2, n, vis2_m) *
        IntArray::full(sid, n, sid_m)
  */
  while (cur != (void *)0) {
    int v;
    /*@ Given head processed rem vis2_m sid_m */
    /*@ Assert
        exists vdata rest next_ptr,
          cur != 0 &&
          v == vdata &&
          0 <= v && v < n && n <= 2147483647 &&
          rem == cons(vdata, rest) &&
          safeExec(pre_dfs2(g, vis2_m, sid_m),
                   dfs_scc_from(root, u, edges_of(u, processed)), X) &&
          SllPtrArray::missing_i(fadj, n, u, head, fadj_rows) *
          sllseg(head, cur, processed) *
          store(&(cur->data), vdata) * store(&(cur->next), next_ptr) *
          sll(next_ptr, rest) *
          IntArray::full(vis2, n, vis2_m) *
          IntArray::full(sid, n, sid_m)
    */
    v = cur->data;

    if (vis2[v] == 0) {
      /*@ Assert
          root == root@pre && u == u@pre && n == n@pre &&
          fadj == fadj@pre && vis2 == vis2@pre && sid == sid@pre &&
          cur != 0 &&
          0 <= root && root < n && 0 <= u && u < n && 0 <= v && v < n &&
          n <= 2147483647 &&
          Znth(v, vis2_m, 0) == 0 &&
          safeExec(pre_dfs2(g, vis2_m, sid_m),
                   dfs_scc(root, v), X) &&
          SllPtrArray::full(fadj, n, fadj_rows) *
          IntArray::full(vis2, n, vis2_m) *
          IntArray::full(sid, n, sid_m)
      */
      dfs2(root, v, n, fadj, vis2, sid)
          /*@ where(low_level_spec)
                g = g,
                vis2_l = vis2_m, sid_l = sid_m,
                fadj_rows = fadj_rows,
                X = X */;
    }

    /*@ Assert
        exists vdata_ rest_ next_ptr_ vis2_m_ sid_m_,
          root == root@pre && u == u@pre && n == n@pre &&
          fadj == fadj@pre && vis2 == vis2@pre && sid == sid@pre &&
          cur != 0 && v == vdata_ &&
          0 <= root && root < n && 0 <= u && u < n && n <= 2147483647 &&
          rem == cons(vdata_, rest_) &&
          safeExec(pre_dfs2(g, vis2_m_, sid_m_),
                   dfs_scc_from(root, u, edges_of(u, processed)), X) &&
          SllPtrArray::missing_i(fadj, n, u, head, fadj_rows) *
          sllseg(head, cur, processed) *
          store(&(cur->data), vdata_) * store(&(cur->next), next_ptr_) *
          sll(next_ptr_, rest_) *
          IntArray::full(vis2, n, vis2_m_) *
          IntArray::full(sid, n, sid_m_)
    */
    cur = cur->next;
  }

  /* Loop exit: DFS_scc's break branch only breaks (no set_finish / no
     timer, unlike dfs1).  With the cursor exhausted, all forward edges
     of u are in the processed set, so dfs_scc_from(root, u, all edges)
     has nothing left to do — it equals return(tt) under the closure
     assumption of the break branch. */
  /*@ Assert
      exists head vis2_m sid_m,
        root == root@pre && u == u@pre && n == n@pre &&
        fadj == fadj@pre && vis2 == vis2@pre && sid == sid@pre &&
        0 <= root && root < n && 0 <= u && u < n && n <= 2147483647 &&
        safeExec(pre_dfs2(g, vis2_m, sid_m),
                 return(tt), X) &&
        SllPtrArray::missing_i(fadj, n, u, head, fadj_rows) *
        sll(head, Znth(u, fadj_rows, nil)) *
        store(&cur, struct list*, 0) *
        IntArray::full(vis2, n, vis2_m) *
        IntArray::full(sid, n, sid_m)
  */
}

/* kosaraju_finish: outer Phase-1 loop, refines kosaraju_finish_monad.
   A deterministic for(i<n) over the vertex range is an angelic realization
   of pick_unvisited1 (every unvisited vertex is eventually visited).  The
   loop body calls dfs1(i) (a DIFFERENT function, not self-recursion), so
   symexec has no recursion-prefill point here; the dfs1 call uses its own
   low_level_spec.  Inv expresses: vertices 0..i-1 already attempted, the
   monad continuation is kosaraju_finish_from(i). */
void kosaraju_finish(int n, struct list **radj, int *vis1, int *fin, int *timer_p)
/*@ low_level_spec
    With g vis1_l vis2_l_abs fin_l sid_l_abs timer_v scc_next_v_abs X radj_rows
    Require
      safeExec(pre_kosaraju(g, vis1_l, vis2_l_abs, fin_l, sid_l_abs, timer_v, scc_next_v_abs),
               kosaraju_finish_monad, X) &&
      0 <= n && n <= 2147483647 &&
      SllPtrArray::full(radj, n, radj_rows) *
      IntArray::full(vis1, n, vis1_l) *
      IntArray::full(fin, n, fin_l) *
      IntArray::full(timer_p, 1, cons(timer_v, nil))
    Ensure
      exists vis1_l_ fin_l_ timer_v_,
      safeExec(pre_kosaraju(g, vis1_l_, vis2_l_abs, fin_l_, sid_l_abs, timer_v_, scc_next_v_abs),
               return(tt), X) &&
      SllPtrArray::full(radj, n, radj_rows) *
      IntArray::full(vis1, n, vis1_l_) *
      IntArray::full(fin, n, fin_l_) *
      IntArray::full(timer_p, 1, cons(timer_v_, nil))
 */
{
  int i;
    /*@ Inv Assert
        exists vis1_m fin_m timer_m,
          safeExec(pre_kosaraju(g, vis1_m, vis2_l_abs, fin_m, sid_l_abs, timer_m, scc_next_v_abs),
                   kosaraju_finish_from(i), X) &&
          n == n@pre &&
          radj == radj@pre && vis1 == vis1@pre && fin == fin@pre &&
          timer_p == timer_p@pre &&
          0 <= i && i <= n && n <= 2147483647 &&
          SllPtrArray::full(radj, n, radj_rows) *
          IntArray::full(vis1, n, vis1_m) *
          IntArray::full(fin, n, fin_m) *
          IntArray::full(timer_p, 1, cons(timer_m, nil))
    */
  for (i = 0; i < n; i++) {
    if (vis1[i] == 0) {
      /*@ Given vis1_m fin_m timer_m */
      /*@ Assert
          n == n@pre &&
          radj == radj@pre && vis1 == vis1@pre && fin == fin@pre &&
          timer_p == timer_p@pre &&
          0 <= i && i < n && n <= 2147483647 &&
          Znth(i, vis1_m, 0) == 0 &&
          safeExec(pre_dfs1(g, vis1_m, fin_m, timer_m),
                   dfs_finish(i), X) &&
          SllPtrArray::full(radj, n, radj_rows) *
          IntArray::full(vis1, n, vis1_m) *
          IntArray::full(fin, n, fin_m) *
          IntArray::full(timer_p, 1, cons(timer_m, nil))
      */
      dfs1(i, n, radj, vis1, fin, timer_p)
          /*@ where(low_level_spec)
                g = g,
                vis1_l = vis1_m, fin_l = fin_m, timer_v = timer_m,
                radj_rows = radj_rows,
                X = X */;
    }
  }
}

/* kosaraju_scc: outer Phase-2 loop, refines kosaraju_scc_monad.
   Driven by a pre-sorted order[] array (finish descending), so the loop
   visits roots in finish-descending order — a deterministic realization
   of pick_unvisited2 (maximal finish).  order_sorted(order_l, fin_l) is a
   precondition (its proof is deferred).  For each k, u = order[k]; if u
   is unvisited2, assign a fresh scc id and dfs2(u,u).  dfs2 is a DIFFERENT
   function call (not self-recursion), using its own low_level_spec. */
void kosaraju_scc(int n, struct list **fadj, int *vis2, int *sid, int *scc_next_p, int *order, int *fin)
/*@ low_level_spec
    With g vis1_l_abs vis2_l sid_l timer_v_abs scc_next_v order_l fin_l X fadj_rows
    Require
      safeExec(pre_kosaraju(g, vis1_l_abs, vis2_l, fin_l, sid_l, timer_v_abs, scc_next_v),
               kosaraju_scc_monad, X) &&
      order_sorted(order_l, fin_l) &&
      (forall (j: Z), (0 <= j && j < n) => (0 <= Znth(j, order_l, 0) && Znth(j, order_l, 0) < n)) &&
      0 <= n && n <= 2147483647 &&
      SllPtrArray::full(fadj, n, fadj_rows) *
      IntArray::full(vis2, n, vis2_l) *
      IntArray::full(sid, n, sid_l) *
      IntArray::full(scc_next_p, 1, cons(scc_next_v, nil)) *
      IntArray::full(order, n, order_l) *
      IntArray::full(fin, n, fin_l)
    Ensure
      exists vis2_l_ sid_l_ scc_next_v_,
      safeExec(pre_kosaraju(g, vis1_l_abs, vis2_l_, fin_l, sid_l_, timer_v_abs, scc_next_v_),
               return(tt), X) &&
      SllPtrArray::full(fadj, n, fadj_rows) *
      IntArray::full(vis2, n, vis2_l_) *
      IntArray::full(sid, n, sid_l_) *
      IntArray::full(scc_next_p, 1, cons(scc_next_v_, nil)) *
      IntArray::full(order, n, order_l) *
      IntArray::full(fin, n, fin_l)
 */
{
  int k;
    /*@ Inv Assert
        exists vis2_m sid_m scc_next_m,
          safeExec(pre_kosaraju(g, vis1_l_abs, vis2_m, fin_l, sid_m, timer_v_abs, scc_next_m),
                   kosaraju_scc_from(k), X) &&
          order_sorted(order_l, fin_l) &&
          (forall (j: Z), (0 <= j && j < n) => (0 <= Znth(j, order_l, 0) && Znth(j, order_l, 0) < n)) &&
          n == n@pre &&
          fadj == fadj@pre && vis2 == vis2@pre && sid == sid@pre &&
          scc_next_p == scc_next_p@pre && order == order@pre && fin == fin@pre &&
          0 <= k && k <= n && n <= 2147483647 &&
          SllPtrArray::full(fadj, n, fadj_rows) *
          IntArray::full(vis2, n, vis2_m) *
          IntArray::full(sid, n, sid_m) *
          IntArray::full(scc_next_p, 1, cons(scc_next_m, nil)) *
          IntArray::full(order, n, order_l) *
          IntArray::full(fin, n, fin_l)
    */
  for (k = 0; k < n; k++) {
    /*@ Given vis2_m sid_m scc_next_m */
    int u = order[k];
    /*@ Assert
        n == n@pre &&
        fadj == fadj@pre && vis2 == vis2@pre && sid == sid@pre &&
        scc_next_p == scc_next_p@pre && order == order@pre && fin == fin@pre &&
        0 <= k && k < n && n <= 2147483647 &&
        u == Znth(k, order_l, 0) &&
        0 <= u && u < n && n <= 2147483647 &&
        safeExec(pre_kosaraju(g, vis1_l_abs, vis2_m, fin_l, sid_m, timer_v_abs, scc_next_m),
                 kosaraju_scc_from(k), X) &&
        SllPtrArray::full(fadj, n, fadj_rows) *
        IntArray::full(vis2, n, vis2_m) *
        IntArray::full(sid, n, sid_m) *
        IntArray::full(scc_next_p, 1, cons(scc_next_m, nil)) *
        IntArray::full(order, n, order_l) *
        IntArray::full(fin, n, fin_l)
    */
    if (vis2[u] == 0) {
      /*@ Assert
          n == n@pre &&
          fadj == fadj@pre && vis2 == vis2@pre && sid == sid@pre &&
          scc_next_p == scc_next_p@pre && order == order@pre && fin == fin@pre &&
          0 <= k && k < n && n <= 2147483647 &&
          0 <= u && u < n && n <= 2147483647 &&
          Znth(u, vis2_m, 0) == 0 &&
          safeExec(pre_kosaraju(g, vis1_l_abs, vis2_m, fin_l, sid_m, timer_v_abs, scc_next_m),
                   kosaraju_scc_from(k), X) &&
          SllPtrArray::full(fadj, n, fadj_rows) *
          IntArray::full(vis2, n, vis2_m) *
          IntArray::full(sid, n, sid_m) *
          IntArray::full(scc_next_p, 1, cons(scc_next_m, nil)) *
          IntArray::full(order, n, order_l) *
          IntArray::full(fin, n, fin_l)
      */
      sid[u] = scc_next_p[0];
      scc_next_p[0] = scc_next_p[0] + 1;
      dfs2(u, u, n, fadj, vis2, sid)
          /*@ where(low_level_spec)
                g = g,
                root = u, u = u,
                vis2_l = vis2_m, sid_l = sid_m,
                fadj_rows = fadj_rows,
                X = X */;
    }
  }
}

/* kosaraju_run: top-level driver, refines kosaraju_monad (finish ;; scc).
   Two DIFFERENT-function calls in sequence; each uses its own low_level_spec.
   The outer frame relates the full state to kosaraju_monad via pre_kosaraju. */
void kosaraju_run(int n, struct list **radj, struct list **fadj,
                  int *vis1, int *vis2, int *fin, int *sid,
                  int *timer_p, int *scc_next_p, int *order)
/*@ low_level_spec
    With g vis1_l vis2_l fin_l sid_l timer_v scc_next_v order_l X radj_rows fadj_rows
    Require
      safeExec(pre_kosaraju(g, vis1_l, vis2_l, fin_l, sid_l, timer_v, scc_next_v),
               kosaraju_monad, X) &&
      order_sorted(order_l, fin_l) &&
      (forall (j: Z), (0 <= j && j < n) => (0 <= Znth(j, order_l, 0) && Znth(j, order_l, 0) < n)) &&
      0 <= n && n <= 2147483647 &&
      SllPtrArray::full(radj, n, radj_rows) *
      SllPtrArray::full(fadj, n, fadj_rows) *
      IntArray::full(vis1, n, vis1_l) *
      IntArray::full(vis2, n, vis2_l) *
      IntArray::full(fin, n, fin_l) *
      IntArray::full(sid, n, sid_l) *
      IntArray::full(timer_p, 1, cons(timer_v, nil)) *
      IntArray::full(scc_next_p, 1, cons(scc_next_v, nil)) *
      IntArray::full(order, n, order_l)
    Ensure
      exists vis1_l_ vis2_l_ fin_l_ sid_l_ timer_v_ scc_next_v_,
      safeExec(pre_kosaraju(g, vis1_l_, vis2_l_, fin_l_, sid_l_, timer_v_, scc_next_v_),
               return(tt), X) &&
      SllPtrArray::full(radj, n, radj_rows) *
      SllPtrArray::full(fadj, n, fadj_rows) *
      IntArray::full(vis1, n, vis1_l_) *
      IntArray::full(vis2, n, vis2_l_) *
      IntArray::full(fin, n, fin_l_) *
      IntArray::full(sid, n, sid_l_) *
      IntArray::full(timer_p, 1, cons(timer_v_, nil)) *
      IntArray::full(scc_next_p, 1, cons(scc_next_v_, nil)) *
      IntArray::full(order, n, order_l)
 */
{
  kosaraju_finish(n, radj, vis1, fin, timer_p)
      /*@ where(low_level_spec)
            g = g,
            vis1_l = vis1_l, vis2_l_abs = vis2_l, fin_l = fin_l,
            sid_l_abs = sid_l, timer_v = timer_v, scc_next_v_abs = scc_next_v,
            radj_rows = radj_rows,
            X = X */;
  kosaraju_scc(n, fadj, vis2, sid, scc_next_p, order, fin)
      /*@ where(low_level_spec)
            g = g,
            vis1_l_abs = vis1_l, vis2_l = vis2_l, sid_l = sid_l,
            timer_v_abs = timer_v, scc_next_v = scc_next_v,
            order_l = order_l, fin_l = fin_l,
            fadj_rows = fadj_rows,
            X = X */;
}
