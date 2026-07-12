# Tarjan Directed SCC Monad Interface for C Refinement

**Source directory**: `SeparationLogic/algorithms/Tarjan_directed`

This note is for downstream C refinement work.  It summarizes the Monad-level
objects and theorems that the C proof should connect to, and separates the
stable interface from proof-local invariants.

## Recommended Imports

For the final refinement theorem, downstream proofs should normally import the
correctness file, which re-exports the program and invariant layers it uses:

```coq
From Algorithms.Tarjan_directed Require Import Tarjan_scc_correctness.
```

When only the abstract SCC specification is needed, import:

```coq
From Algorithms.Tarjan_directed Require Import SCC_basic.
```

The implementation is parameterized by:

```coq
Context {V E : Type}
        `{EqDec V eq}
        (g : OriginalGraphType V E)
        `{OriginalGraph_gvalid g}.
```

`OriginalGraphType` comes from `GraphLib.examples.tarjan`.  In this development
it is used as a directed graph: an edge `e` goes from
`original_step_fst g e` to `original_step_snd g e`.

## Abstract Graph and SCC Specification

`SCC_basic.v` provides the graph-theoretic specification used by the final
correctness theorem.

```coq
dg_step g x y : Prop
```

There is a directed edge from `x` to `y`.

```coq
dg_reachable g x y : Prop
```

There is a directed path from `x` to `y`; this is the reflexive-transitive
closure of `dg_step`.

```coq
mutually_reachable g u v : Prop
```

`u` reaches `v` and `v` reaches `u`.

```coq
is_SCC g C : Prop
```

`C : V -> Prop` is a mathematical strongly connected component: it is
non-empty, internally mutually reachable, and maximal under mutual reachability.

```coq
scc_partition g sccs : Prop
```

`sccs : list (V -> Prop)` covers every valid vertex, every listed component is
an `is_SCC`, and overlapping listed components are extensionally equal.

Useful lemmas include:

```coq
mutually_reachable_refl
mutually_reachable_sym
mutually_reachable_trans
is_SCC_closed_under_mr
is_SCC_extensional
mutually_reachable_same_SCC
scc_partition_unique_SCC
```

These are the main bridge lemmas to use after the C-side memory representation
has been related to the abstract output `sccs`.

## Monad State

`Tarjan_scc.v` defines the abstract algorithm state:

```coq
Record SCCSt := mkSCCSt {
  visited : V -> Prop;
  timer   : nat;
  fa      : V -> V;
  dfn     : V -> nat;
  low     : V -> nat;
  stack   : list V;
  sccs    : list (V -> Prop);
}.
```

Field meanings for refinement:

| Field | Meaning |
| --- | --- |
| `visited` | Vertices discovered by DFS. |
| `timer` | Next discovery number; `initSt` starts from `1`. |
| `fa` | DFS parent map.  A self-parent means no assigned parent. |
| `dfn` | Discovery number.  Unvisited vertices initially have `0`. |
| `low` | Low-link value.  Unvisited vertices initially have `0`. |
| `stack` | Active Tarjan stack, with the top at the list head. |
| `sccs` | Emitted SCCs.  Each component is represented as a predicate `V -> Prop`. |

The initial state is:

```coq
initSt =
  mkSCCSt
    (fun _ => False)
    1
    (fun v => v)
    (fun _ => 0)
    (fun _ => 0)
    nil
    nil.
```

For C refinement, the concrete C state should be related to an `SCCSt`.  The
usual relation should expose at least:

- the C visited marks as `visited s`;
- the DFS timer as `timer s`;
- the parent array as `fa s`;
- discovery and low arrays as `dfn s` and `low s`;
- the C stack contents as `stack s`, preserving head/top direction;
- the emitted SCC representation as `sccs s`, or an equivalent structure that
  can later be converted to `scc_partition g (sccs s)`.

## Monad Program Entry Points

Single-root DFS:

```coq
tarjan_scc g u : program SCCSt unit
```

It runs Tarjan DFS from one unvisited root `u`.

Whole-graph algorithm:

```coq
tarjan_scc_all g : program SCCSt unit
```

It iterates over all `original_vvalid g` vertices and starts `tarjan_scc g v`
whenever `v` is not yet visited.

Primitive operations in `Tarjan_scc.v` describe the abstract steps that the C
implementation should simulate:

```coq
visit
set_dfn
set_low
set_fa
incr_timer
push_stack
update_low
pop_scc
preloop
process_edge
```

The most important operational convention is `pop_scc`: it uses
`stack_split_at (stack s) u` and emits the popped prefix as
`fun v => In v popped`.  Therefore, the C pop loop should correspond to popping
from the stack top until and including `u`.

## Final Correctness Theorem

The main theorem for downstream refinement is:

```coq
tarjan_scc_all_outputs_scc_partition :
  Hoare
    (fun s => s = initSt)
    (tarjan_scc_all g)
    (fun _ s => scc_partition g (sccs s)).
```

This is the theorem the C refinement should ultimately reuse.  A typical final
C theorem should show that the C program refines `tarjan_scc_all g` from a
concrete initialization corresponding to `initSt`; then this theorem supplies
the mathematical SCC partition property of the abstract output.

Two useful supporting theorems are:

```coq
tarjan_scc_all_visited_all :
  Hoare
    (fun _ => True)
    (tarjan_scc_all g)
    (fun _ s => forall v, original_vvalid g v -> Sets.In v (visited s)).

tarjan_scc_all_preserves_output_inv_and_empty_stack :
  Hoare
    (fun s => s = initSt)
    (tarjan_scc_all g)
    (fun _ s => SCCsOutputInv g s /\ stack s = nil).
```

`tarjan_scc_all_outputs_scc_partition` is already assembled from these facts, so
the C proof usually should not need to replay the output-correctness argument.

## DFS Tree and Low-Link Interface

Several proofs describe the abstract DFS tree induced by the state:

```coq
state_to_dfs_tree g s root : OriginalGraphType V E
```

Its vertices are exactly `visited s`, and its edges are the assigned parent
edges from `fa`.

Useful structural facts:

```coq
state_to_dfs_tree_vvalid :
  original_vvalid (state_to_dfs_tree g s root) v <->
  Sets.In v (visited s).

tree_step_char :
  dg_step (state_to_dfs_tree g s root) x y ->
  fa s y = x /\ fa s y <> y /\ Sets.In y (visited s).

tree_step_char_backward :
  dg_step g x y ->
  fa s y = x ->
  fa s y <> y ->
  Sets.In y (visited s) ->
  dg_step (state_to_dfs_tree g s root) x y.
```

`Tarjan_scc_is_low.v` defines the public low-link specification:

```coq
scc_low_reachable g root s x y : Prop
scc_is_low_v g root s u : Prop
scc_is_low g root s : Prop
```

The intended meaning is: `low s u` is the minimum `dfn` among vertices reachable
from the DFS subtree of `u` by zero or more tree edges plus at most one active
non-tree edge.  C refinement can use this as a semantic guide for loop
invariants, but the final C theorem should normally depend on
`tarjan_scc_all_outputs_scc_partition`, not on re-proving low-link correctness.

## Stable Boundary for C Refinement

Use these as stable cross-layer interfaces:

- `SCCSt`, `initSt`, `tarjan_scc`, and `tarjan_scc_all`;
- `dg_step`, `dg_reachable`, `mutually_reachable`, `is_SCC`, and
  `scc_partition`;
- the final theorem `tarjan_scc_all_outputs_scc_partition`;
- simple state-shape facts such as `state_to_dfs_tree_vvalid`,
  `tree_step_char`, and `tree_step_char_backward`;
- output bridge predicates from `Tarjan_scc_correctness.v` when needed:
  `SCCsOutputInv`, `AllVerticesVisited`, and `SCCsPartitionReady`.

Treat the following as proof-internal unless a C proof genuinely needs a local
simulation invariant:

- `RootPrePop`, `RootPreMaybePop`, `RootAfterMaybePop`, `RootFinal`;
- `LoopInv`, `LoopCoreInv`, `LoopCoreShape`, `LoopAuxFacts`;
- nested-frame contracts such as `VisitContract`, `VisitFrameContract`, and
  `ChildContributionContract`;
- closedness and low-link restoration cuts such as `Closed`,
  `PoppedSegmentClosed`, and `PoppedSegmentNoActiveReach`.

Those predicates are useful references for designing C loop invariants, but
they are not intended to be the final public specification of the C algorithm.

## Suggested Refinement Shape

The downstream proof can be organized around this contract:

```coq
(* Pseudocode shape, not an existing theorem name. *)
Theorem C_tarjan_refines_monad :
    concrete_initial_state cst initSt ->
    c_program_exec cst cst' ->
  exists s',
    Sets.In (initSt, tt, s') (tarjan_scc_all g) /\
    concrete_final_state cst' s'.
```

Then combine it with:

```coq
tarjan_scc_all_outputs_scc_partition
```

to obtain the final SCC partition property.  If the C program returns a concrete
component array instead of the abstract `list (V -> Prop)`, add a separate
representation theorem proving that the concrete result denotes `sccs s'`.

## Practical Notes

- The algorithm is nondeterministic at the Monad level because `forset` may
  choose vertices in any order.  The C implementation can use a concrete order;
  refinement only needs to show that its order is one valid `forset` execution.
- `sccs` order is not semantically important.  The final specification is
  `scc_partition`, not equality with a particular list order.
- `stack` order is semantically important during simulation: the list head is
  the active stack top.
- `dfn` starts at `1`; `0` is reserved by the initial state for unvisited
  vertices.
- `fa v = v` is the abstract representation of "no parent assigned".
- `update_low u n` only changes `low u` when `n < low u`.
- The final theorem does not require exposing `dfn`, `low`, `fa`, or `stack` to
  users of the verified C program; they are refinement witnesses.
