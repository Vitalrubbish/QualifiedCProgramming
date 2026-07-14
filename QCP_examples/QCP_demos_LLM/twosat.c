#include "kosaraju_rel.c"

/*@ Import Coq From SimpleC.EE.QCP_demos_LLM Require Import twosat_lib */

/*@ Extern Coq
    (twosat_csr_wf : Z -> list Z -> list Z -> list Z -> list Z -> Prop)
    (no_conflict_by_sid : list Z -> Z -> Prop)
     */

/* ==================================================================== */
/* Vertex encoding functions                                            */
/*                                                                       */
/* Variable v (1-indexed, 1 <= v <= n) → two literals:                   */
/*   vertex 2*(v-1)   = literal (v, true)   (even)                      */
/*   vertex 2*(v-1)+1 = literal (v, false)  (odd)                       */
/*                                                                       */
/* C int encoding: positive → true, negative → false                     */
/*   lit_vertex(a) = 2*(|a|-1) + (a<0)                                   */
/*   neg_vertex(a) = lit_vertex(-a) = lit_vertex(a) XOR 1                */
/* ==================================================================== */

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

int lit_vertex(int a)
  /*@ Require INT_MIN < a && a != 0 && emp
      Ensure (a > 0 => __return == 2 * (a - 1)) &&
              (a < 0 => __return == 2 * (-a - 1) + 1) && emp
   */
{
    int abs_a = a > 0 ? a : -a;
    return 2 * (abs_a - 1) + (a < 0 ? 1 : 0);
}

int neg_vertex(int a)
  /*@ Require INT_MIN < a && a != 0 && emp
      Ensure (a > 0 => __return == 2 * a - 1) &&
              (a < 0 => __return == -2 * a - 2) && emp
   */
{
    return lit_vertex(-a);
}

/* ==================================================================== */
/* main: 2SAT satisfiability via implication graph + Kosaraju SCC       */
/*                                                                      */
/* Input:                                                                */
/*   n     = number of boolean variables (1..n)                         */
/*   m     = number of clauses                                          */
/*   lit1  = array of m ints: first literal of each clause (lit1[i] OR lit2[i]) */
/*   lit2  = array of m ints: second literal of each clause (lit1[i] OR lit2[i]) */
/*                                                                       */
/* Builds the implication graph as CSR arrays (fadj/radj), runs          */
/* Kosaraju (dfs1 on reverse graph, dfs2 on forward graph in decreasing  */
/* finish order), then checks whether any variable has both literals      */
/* in the same SCC (UNSAT) or all are in different SCCs (SAT).           */
/*                                                                       */
/* Returns: 0 = satisfiable, 1 = unsatisfiable.                          */

/*          g                  AdjGraph for the implication graph       */
/*          radj_col_l         reverse-graph CSR column list            */
/*          radj_row_l         reverse-graph CSR row list               */
/*          fadj_col_l         forward-graph CSR column list            */
/*          fadj_row_l         forward-graph CSR row list               */
/*          vis1_l fin_l       dfs1 visited / finish lists              */
/*          timer_v            dfs1 timer Z-value                        */
/*          vis2_l sid_l       dfs2 visited / scc-id lists              */
/*          X1 X2              monadic continuations for dfs1 / dfs2    */
/* ==================================================================== */
int main(int n, int m, int *lit1, int *lit2)
  /*@ With
        lit1_l lit2_l
      Require
        n > 0 && m > 0 &&
        IntArray::full(lit1, m, lit1_l) *
        IntArray::full(lit2, m, lit2_l) &&
        m < 1073741824 && n < 1073741824 &&
        (forall (k : Z), (0 <= k && k < m) => Znth(k, lit1_l, 0) != 0 && -n <= Znth(k, lit1_l, 0) && Znth(k, lit1_l, 0) <= n) &&
        (forall (k : Z), (0 <= k && k < m) => Znth(k, lit2_l, 0) != 0 && -n <= Znth(k, lit2_l, 0) && Znth(k, lit2_l, 0) <= n)
      Ensure
        emp
   */
{
    int verts = 2 * n;
    int total_edges = 2 * m;

    /* ---- CSR row arrays (size verts+1, last entry = total edges) ---- */
    int *fadj_row = malloc_int_array(verts + 1);
    int *radj_row = malloc_int_array(verts + 1);

    /* ---- CSR column arrays (packed adjacency) ---- */
    int *fadj_col = malloc_int_array(total_edges);
    int *radj_col = malloc_int_array(total_edges);

    /* ---- DFS phase-1 arrays (reverse graph) ---- */
    int *vis1 = malloc_int_array(verts);
    int *fin  = malloc_int_array(verts);
    int *timer_p = malloc_int_array(1);

    /* ---- DFS phase-2 arrays (forward graph) ---- */
    int *vis2 = malloc_int_array(verts);
    int *sid  = malloc_int_array(verts);

    /* ---- Cursor arrays (copies of row pointers for second pass) ---- */
    int *fcur = malloc_int_array(verts + 1);
    int *rcur = malloc_int_array(verts + 1);

    /*@ Inv Assert
        exists fadj_l radj_l fcol_l rcol_l v1l fnl tpl v2l sdl fcl rcl,
        0 <= i && i <= verts + 1 &&
        n == n@pre && m == m@pre &&
        (forall (k : Z), (0 <= k && k < i) => Znth(k, fadj_l, 0) == 0) &&
        (forall (k : Z), (0 <= k && k < i) => Znth(k, radj_l, 0) == 0) &&
        IntArray::full(lit1, m, lit1_l) *
        IntArray::full(lit2, m, lit2_l) *
        IntArray::full(fadj_row, verts + 1, fadj_l) *
        IntArray::full(radj_row, verts + 1, radj_l) *
        IntArray::full(fadj_col, total_edges, fcol_l) *
        IntArray::full(radj_col, total_edges, rcol_l) *
        IntArray::full(vis1, verts, v1l) *
        IntArray::full(fin, verts, fnl) *
        IntArray::full(timer_p, 1, tpl) *
        IntArray::full(vis2, verts, v2l) *
        IntArray::full(sid, verts, sdl) *
        IntArray::full(fcur, verts + 1, fcl) *
        IntArray::full(rcur, verts + 1, rcl)
    */
    for (int i = 0; i <= verts; i++) { fadj_row[i] = 0; radj_row[i] = 0; }
    /*@ Inv Assert
        exists v1l v2l fnl sdl fcol_l rcol_l tpl fcl rcl fadj_l radj_l,
        0 <= i && i <= verts &&
        n == n@pre && m == m@pre &&
        (forall (k : Z), (0 <= k && k < verts + 1) => Znth(k, fadj_l, 0) == 0) &&
        (forall (k : Z), (0 <= k && k < verts + 1) => Znth(k, radj_l, 0) == 0) &&
        (forall (k : Z), (0 <= k && k < i) => Znth(k, v1l, 0) == 0) &&
        (forall (k : Z), (0 <= k && k < i) => Znth(k, v2l, 0) == 0) &&
        (forall (k : Z), (0 <= k && k < i) => Znth(k, fnl, 0) == 0) &&
        (forall (k : Z), (0 <= k && k < i) => Znth(k, sdl, 0) == 0) &&
        IntArray::full(lit1, m, lit1_l) *
        IntArray::full(lit2, m, lit2_l) *
        IntArray::full(fadj_row, verts + 1, fadj_l) *
        IntArray::full(radj_row, verts + 1, radj_l) *
        IntArray::full(fadj_col, total_edges, fcol_l) *
        IntArray::full(radj_col, total_edges, rcol_l) *
        IntArray::full(vis1, verts, v1l) *
        IntArray::full(fin, verts, fnl) *
        IntArray::full(timer_p, 1, tpl) *
        IntArray::full(vis2, verts, v2l) *
        IntArray::full(sid, verts, sdl) *
        IntArray::full(fcur, verts + 1, fcl) *
        IntArray::full(rcur, verts + 1, rcl)
    */
    for (int i = 0; i < verts; i++) { vis1[i] = 0; vis2[i] = 0; fin[i] = 0; sid[i] = 0; }

    /*@ Inv Assert
        exists fadj_l radj_l fcol_l rcol_l v1l fnl tpl v2l sdl fcl rcl,
        0 <= i && i <= verts &&
        n == n@pre && m == m@pre &&
        IntArray::full(lit1, m, lit1_l) *
        IntArray::full(lit2, m, lit2_l) *
        IntArray::full(fadj_row, verts + 1, fadj_l) *
        IntArray::full(radj_row, verts + 1, radj_l) *
        IntArray::full(fadj_col, total_edges, fcol_l) *
        IntArray::full(radj_col, total_edges, rcol_l) *
        IntArray::full(vis1, verts, v1l) *
        IntArray::full(fin, verts, fnl) *
        IntArray::full(timer_p, 1, tpl) *
        IntArray::full(vis2, verts, v2l) *
        IntArray::full(sid, verts, sdl) *
        IntArray::full(fcur, verts + 1, fcl) *
        IntArray::full(rcur, verts + 1, rcl)
    */
    for (int i = 0; i < verts; i++) {
        fadj_row[i + 1] += fadj_row[i];
        radj_row[i + 1] += radj_row[i];
    }
    /* After prefix sum: fadj_row[verts] = radj_row[verts] = total_edges */

    /* ---- Copy row pointers into cursors ---- */
    /*@ Inv Assert
        exists fcl rcl fadj_l radj_l fcol_l rcol_l v1l fnl tpl v2l sdl,
        0 <= i && i <= verts + 1 &&
        n == n@pre && m == m@pre &&
        (forall (k : Z), (0 <= k && k < i) => Znth(k, fcl, 0) == Znth(k, fadj_l, 0)) &&
        (forall (k : Z), (0 <= k && k < i) => Znth(k, rcl, 0) == Znth(k, radj_l, 0)) &&
        IntArray::full(lit1, m, lit1_l) *
        IntArray::full(lit2, m, lit2_l) *
        IntArray::full(fadj_row, verts + 1, fadj_l) *
        IntArray::full(radj_row, verts + 1, radj_l) *
        IntArray::full(fadj_col, total_edges, fcol_l) *
        IntArray::full(radj_col, total_edges, rcol_l) *
        IntArray::full(vis1, verts, v1l) *
        IntArray::full(fin, verts, fnl) *
        IntArray::full(timer_p, 1, tpl) *
        IntArray::full(vis2, verts, v2l) *
        IntArray::full(sid, verts, sdl) *
        IntArray::full(fcur, verts + 1, fcl) *
        IntArray::full(rcur, verts + 1, rcl)
    */
    for (int i = 0; i <= verts; i++) { fcur[i] = fadj_row[i]; rcur[i] = radj_row[i]; }

    /* ---- Process clauses ---- */
    /*@ Inv Assert
        exists fadj_l radj_l fcol_l rcol_l v1l fnl tpl v2l sdl fcl rcl,
        0 <= i && i <= m &&
        n == n@pre && m == m@pre &&
        verts == 2 * n && total_edges == 2 * m &&
        (forall (k : Z), (0 <= k && k < m) => Znth(k, lit1_l, 0) != 0 && -n <= Znth(k, lit1_l, 0) && Znth(k, lit1_l, 0) <= n) &&
        (forall (k : Z), (0 <= k && k < m) => Znth(k, lit2_l, 0) != 0 && -n <= Znth(k, lit2_l, 0) && Znth(k, lit2_l, 0) <= n) &&
        (forall (k : Z), (0 <= k && k < verts + 1) => 0 <= Znth(k, fcl, 0) && Znth(k, fcl, 0) <= total_edges) &&
        (forall (k : Z), (0 <= k && k < verts) => Znth(k, fcl, 0) < total_edges) &&
        (forall (k : Z), (0 <= k && k < verts + 1) => 0 <= Znth(k, rcl, 0) && Znth(k, rcl, 0) <= total_edges) &&
        (forall (k : Z), (0 <= k && k < verts) => Znth(k, rcl, 0) < total_edges) &&
        IntArray::full(lit1, m, lit1_l) *
        IntArray::full(lit2, m, lit2_l) *
        IntArray::full(fadj_row, verts + 1, fadj_l) *
        IntArray::full(radj_row, verts + 1, radj_l) *
        IntArray::full(fadj_col, total_edges, fcol_l) *
        IntArray::full(radj_col, total_edges, rcol_l) *
        IntArray::full(vis1, verts, v1l) *
        IntArray::full(fin, verts, fnl) *
        IntArray::full(timer_p, 1, tpl) *
        IntArray::full(vis2, verts, v2l) *
        IntArray::full(sid, verts, sdl) *
        IntArray::full(fcur, verts + 1, fcl) *
        IntArray::full(rcur, verts + 1, rcl)
    */
    for (int i = 0; i < m; i++) {
        /*@ Given fadj_l radj_l fcol_l rcol_l v1l fnl tpl v2l sdl fcl rcl */
        int const a = lit1[i];
        int const b = lit2[i];
        int const na = a > 0 ? 2 * a - 1 : -2 * a - 2;
        int const nb = b > 0 ? 2 * b - 1 : -2 * b - 2;
        int const va = a > 0 ? 2 * a - 2 : -2 * a - 1;
        int const vb = b > 0 ? 2 * b - 2 : -2 * b - 1;
        /*@ Assert
            0 <= na && na < verts &&
            0 <= nb && nb < verts &&
            0 <= va && va < verts &&
            0 <= vb && vb < verts &&
            0 <= Znth(na, fcl, 0) &&
            (forall (k : Z), (0 <= k && k < m) => Znth(k, lit1_l, 0) != 0 && -n <= Znth(k, lit1_l, 0) && Znth(k, lit1_l, 0) <= n) &&
            (forall (k : Z), (0 <= k && k < m) => Znth(k, lit2_l, 0) != 0 && -n <= Znth(k, lit2_l, 0) && Znth(k, lit2_l, 0) <= n) &&
            (forall (k : Z), (0 <= k && k < verts + 1) => 0 <= Znth(k, fcl, 0) && Znth(k, fcl, 0) <= total_edges) &&
            (forall (k : Z), (0 <= k && k < verts) => Znth(k, fcl, 0) < total_edges) &&
            (forall (k : Z), (0 <= k && k < verts + 1) => 0 <= Znth(k, rcl, 0) && Znth(k, rcl, 0) <= total_edges) &&
            (forall (k : Z), (0 <= k && k < verts) => Znth(k, rcl, 0) < total_edges) &&
            IntArray::full(lit1, m, lit1_l) *
            IntArray::full(lit2, m, lit2_l) *
            IntArray::full(fadj_row, verts + 1, fadj_l) *
            IntArray::full(radj_row, verts + 1, radj_l) *
            IntArray::full(fadj_col, total_edges, fcol_l) *
            IntArray::full(radj_col, total_edges, rcol_l) *
            IntArray::full(vis1, verts, v1l) *
            IntArray::full(fin, verts, fnl) *
            IntArray::full(timer_p, 1, tpl) *
            IntArray::full(vis2, verts, v2l) *
            IntArray::full(sid, verts, sdl) *
            IntArray::full(fcur, verts + 1, fcl) *
            IntArray::full(rcur, verts + 1, rcl)
        */
        int const p = fcur[na];
        int const q = rcur[vb];
        int const r = fcur[nb];
        int const s = rcur[va];
        /*@ Assert
            0 <= na && na < verts &&
            0 <= nb && nb < verts &&
            0 <= va && va < verts &&
            0 <= vb && vb < verts &&
            0 <= p && p < total_edges &&
            0 <= q && q < total_edges &&
            0 <= r && r < total_edges &&
            0 <= s && s < total_edges &&
            (forall (k : Z), (0 <= k && k < m) => Znth(k, lit1_l, 0) != 0 && -n <= Znth(k, lit1_l, 0) && Znth(k, lit1_l, 0) <= n) &&
            (forall (k : Z), (0 <= k && k < m) => Znth(k, lit2_l, 0) != 0 && -n <= Znth(k, lit2_l, 0) && Znth(k, lit2_l, 0) <= n) &&
            (forall (k : Z), (0 <= k && k < verts + 1) => 0 <= Znth(k, fcl, 0) && Znth(k, fcl, 0) <= total_edges) &&
            (forall (k : Z), (0 <= k && k < verts) => Znth(k, fcl, 0) < total_edges) &&
            (forall (k : Z), (0 <= k && k < verts + 1) => 0 <= Znth(k, rcl, 0) && Znth(k, rcl, 0) <= total_edges) &&
            (forall (k : Z), (0 <= k && k < verts) => Znth(k, rcl, 0) < total_edges) &&
            IntArray::full(lit1, m, lit1_l) *
            IntArray::full(lit2, m, lit2_l) *
            IntArray::full(fadj_row, verts + 1, fadj_l) *
            IntArray::full(radj_row, verts + 1, radj_l) *
            IntArray::full(fadj_col, total_edges, fcol_l) *
            IntArray::full(radj_col, total_edges, rcol_l) *
            IntArray::full(vis1, verts, v1l) *
            IntArray::full(fin, verts, fnl) *
            IntArray::full(timer_p, 1, tpl) *
            IntArray::full(vis2, verts, v2l) *
            IntArray::full(sid, verts, sdl) *
            IntArray::full(fcur, verts + 1, fcl) *
            IntArray::full(rcur, verts + 1, rcl)
        */
        fadj_col[p] = vb;
        fcur[na] = p + 1;
        radj_col[q] = na;
        rcur[vb] = q + 1;
        fadj_col[r] = va;
        fcur[nb] = r + 1;
        radj_col[s] = nb;
        rcur[va] = s + 1;
    }



    /* ================================================================ */
    /* Phase 1 (dfs1): reverse-graph DFS                                */
    /* Iterate vertices 0..verts-1, calling dfs1 on each unvisited one.  */
    /* Refines kosaraju_finish (abstract: pick unvisited, DFS_finish).   */
    /* ================================================================ */
    /*@ Inv Assert
        exists fadj_l radj_l fcol_l rcol_l v1l fnl tpl v2l sdl fcl rcl,
        0 <= u && u <= verts &&
        n == n@pre && m == m@pre &&
        IntArray::full(lit1, m, lit1_l) *
        IntArray::full(lit2, m, lit2_l) *
        IntArray::full(fadj_row, verts + 1, fadj_l) *
        IntArray::full(radj_row, verts + 1, radj_l) *
        IntArray::full(fadj_col, total_edges, fcol_l) *
        IntArray::full(radj_col, total_edges, rcol_l) *
        IntArray::full(vis1, verts, v1l) *
        IntArray::full(fin, verts, fnl) *
        IntArray::full(timer_p, 1, tpl) *
        IntArray::full(vis2, verts, v2l) *
        IntArray::full(sid, verts, sdl) *
        IntArray::full(fcur, verts + 1, fcl) *
        IntArray::full(rcur, verts + 1, rcl)
    */
    for (int u = 0; u < verts; u++) {
        if (vis1[u] == 0) {
            dfs1(u, verts, radj_col, radj_row, vis1, fin, timer_p)
                /*@ where(low_level_spec)
                      g = g,
                      radj_col_l = radj_col_l, radj_row_l = radj_row_l,
                      vis1_l = vis1_l, fin_l = fin_l, timer_v = timer_v,
                      X = X1 */;
        }
    }

    /* ================================================================ */
    /* Phase 2 (dfs2): forward-graph DFS in decreasing finish order     */
    /* Scan ALL vertices each iteration for the unvisited vertex with   */
    /* the maximum finish time.  This matches the abstract               */
    /* kosaraju_scc/DFS_scc semantics (pick_unvisited2 selects the      */
    /* unvisited vertex with max finish).  Runs at most verts rounds.   */
    /* ================================================================ */
    {
    /*@ Inv Assert
        exists fadj_l radj_l fcol_l rcol_l v1l fnl tpl v2l sdl fcl rcl,
        0 <= round && round <= verts &&
        n == n@pre && m == m@pre &&
        IntArray::full(lit1, m, lit1_l) *
        IntArray::full(lit2, m, lit2_l) *
        IntArray::full(fadj_row, verts + 1, fadj_l) *
        IntArray::full(radj_row, verts + 1, radj_l) *
        IntArray::full(fadj_col, total_edges, fcol_l) *
        IntArray::full(radj_col, total_edges, rcol_l) *
        IntArray::full(vis1, verts, v1l) *
        IntArray::full(fin, verts, fnl) *
        IntArray::full(timer_p, 1, tpl) *
        IntArray::full(vis2, verts, v2l) *
        IntArray::full(sid, verts, sdl) *
        IntArray::full(fcur, verts + 1, fcl) *
        IntArray::full(rcur, verts + 1, rcl)
    */
    for (int round = 0; round < verts; round++) {
            int best = -1;
            int best_fin = -1;
            /*@ Inv Assert
                exists v2l fnl fadj_l radj_l fcol_l rcol_l v1l tpl sdl fcl rcl,
                0 <= v && v <= verts &&
                n == n@pre && m == m@pre &&
                IntArray::full(lit1, m, lit1_l) *
                IntArray::full(lit2, m, lit2_l) *
                IntArray::full(fadj_row, verts + 1, fadj_l) *
                IntArray::full(radj_row, verts + 1, radj_l) *
                IntArray::full(fadj_col, total_edges, fcol_l) *
                IntArray::full(radj_col, total_edges, rcol_l) *
                IntArray::full(vis1, verts, v1l) *
                IntArray::full(fin, verts, fnl) *
                IntArray::full(timer_p, 1, tpl) *
                IntArray::full(vis2, verts, v2l) *
                IntArray::full(sid, verts, sdl) *
            IntArray::full(fcur, verts + 1, fcl) *
            IntArray::full(rcur, verts + 1, rcl)
        */
        for (int v = 0; v < verts; v++) {
                if (vis2[v] == 0 && fin[v] > best_fin) {
                    best_fin = fin[v];
                    best = v;
                }
            }
            if (best != -1) {
                dfs2(best, best, verts, fadj_col, fadj_row, vis2, sid)
                    /*@ where(low_level_spec)
                          g = g,
                          fadj_col_l = fadj_col_l, fadj_row_l = fadj_row_l,
                          vis2_l = vis2_l, sid_l = sid_l,
                          root_v = best,
                          X = X2 */;
            }
        }
    }

    /* ================================================================ */
    /* Conflict check                                                    */
    /* For each variable v, if sid[2*(v-1)] == sid[2*(v-1)+1], the two   */
    /* literals are in the same SCC → unsatisfiable.                    */
    /* ================================================================ */
    int result = 0;
    /*@ Inv Assert
        exists sdl v2l fadj_l radj_l fcol_l rcol_l v1l fnl tpl fcl rcl,
        1 <= u && u <= n + 1 && (result == 0 || result == 1) &&
        n == n@pre && m == m@pre &&
        (result == 0 => (forall (v : Z), (1 <= v && v < u) => Znth(2*(v-1), sdl, 0) <> Znth(2*(v-1)+1, sdl, 0))) &&
        (result == 1 => exists (vw : Z), (1 <= vw && vw < u) && Znth(2*(vw-1), sdl, 0) == Znth(2*(vw-1)+1, sdl, 0)) &&
        IntArray::full(lit1, m, lit1_l) *
        IntArray::full(lit2, m, lit2_l) *
        IntArray::full(fadj_row, verts + 1, fadj_l) *
        IntArray::full(radj_row, verts + 1, radj_l) *
        IntArray::full(fadj_col, total_edges, fcol_l) *
        IntArray::full(radj_col, total_edges, rcol_l) *
        IntArray::full(vis1, verts, v1l) *
        IntArray::full(fin, verts, fnl) *
        IntArray::full(timer_p, 1, tpl) *
        IntArray::full(vis2, verts, v2l) *
        IntArray::full(sid, verts, sdl) *
        IntArray::full(fcur, verts + 1, fcl) *
        IntArray::full(rcur, verts + 1, rcl)
    */
    for (int u = 1; u <= n && result == 0; u++) {
        if (sid[2 * (u - 1)] == sid[2 * (u - 1) + 1]) {
            result = 1;
        }
    }

    /* ---- Free all allocated arrays ---- */
    free_int_array(fadj_row);
    free_int_array(radj_row);
    free_int_array(fadj_col);
    free_int_array(radj_col);
    free_int_array(fcur);
    free_int_array(rcur);
    free_int_array(vis1);
    free_int_array(fin);
    free_int_array(timer_p);
    free_int_array(vis2);
    free_int_array(sid);

    return result;
}