import SearchAlgorithms.DijkstraGen
import SearchAlgorithms.MultigoalGen
import BenchAux

/-!
# Performance comparison: original vs. generator-based Dijkstra

Standalone executable (`lake exe bench`) comparing the *original* enumeration-based
`dijkstra` against the generator-based `dijkstra_gen`.

* `dijkstra` expands a node by iterating over **all** vertices of the graph and filtering
  them by the adjacency relation, so every expansion **step** costs `Θ(|V|)`.
* `dijkstra_gen` expands a node by iterating over its explicit neighbour list
  `G.neighbours`, so an expansion **step** costs `Θ(out-degree)` — independent of `|V|`.

Both are proved to return the same result (`dijkstra_gen_eq`), so this only measures
wall-clock time.

**End-to-end behaviour (measured).**  The `Θ(out-degree)` figure above is the cost of a single
*expansion step*.  The full `dijkstra_gen` call is now also flat in `|V|` end-to-end: Experiment
3 runs a depth-100 search on graphs up to one **billion** vertices in ≈ 200 ms each.  This relies
on the generator algorithms using the `nodeNum`-free termination metric
`hsearch_termination_metric_nat` (valued in `ℕ × ℕ × ℕ × ℕ`).  Previously the core used a metric
of type `Vector _ g.nodeNum`, and constructing that type's well-founded-relation dictionary made
the compiler evaluate `g.nodeNum = Fintype.card V` once per call; for a `FinEnum` graph that
enumerates the whole vertex set (`FinEnum.toList (Fin n)` is not stack-safe), so the end-to-end
time was `≈ |V|²` and the program crashed beyond `|V| ≈ 6.5 × 10⁴`.  A termination metric is only
used inside the (erased) well-foundedness proof and is never computed at run time, so switching
to a `nodeNum`-free metric type removes the enumeration entirely while keeping
`dijkstra_gen_eq`/`astar_gen_eq` (hence all correctness proofs) intact.

## Benchmark graph

Each vertex `i` of `Fin n` has out-edges to `i+1, i+2, i+3` (constant out-degree 3) with unit
edge weights.  Graphs are built with the size-independent `toList_univ_finEnum_eq_finRange`
(see `BenchAux`), so no per-size `by decide` is needed.

## Methodology notes (for reproducible numbers)

* Experiments 1–2 use graphs of a **fixed concrete size** (`Fin n`, numeral `n`); Experiment 3
  varies `|V|` and so passes the size as a run-time argument (helper `timePathGen`).  A concrete
  numeral is faster (the `FinEnum`/`DecidableEq` dictionaries are not boxed), but a *closed*
  search expression (concrete graph **and** literal endpoints) is lifted by the compiler and
  evaluated at **module initialisation**, i.e. before `main` runs — with the original
  billion-vertex literals this hung the whole executable at startup.  Keeping at least one
  argument (the goal, or the size) a run-time value keeps the search inside the timed region.
* The result is inspected with the helper `foundPath` (a constructor `match`) rather than
  `Option.isSome`, which was observed to trigger a large, unexpected slowdown here.

## Note on the largest sizes

Experiment 3 now runs at `|V|` up to `10⁹`.  Because the generator search never materialises the
full vertex set at run time (its termination metric is `nodeNum`-free), the depth-100 searches
complete in ≈ 200 ms regardless of `|V|`, with no stack overflow.
-/

open WeightedDiGraph NatGraph

set_option maxRecDepth 10000

/-- Whether a search returned a path.  Uses a plain constructor `match` (compiled to
`Option.casesOn`) instead of `Option.isSome`: both only inspect the head constructor, but
`Option.isSome` was observed to trigger a large, unexpected slowdown in this benchmark. -/
@[inline] def foundPath {α : Type} : Option α → Bool
  | some _ => true
  | none   => false

/-- Sparse neighbour function: `i ↦ [i+1, i+2, i+3]` (dropping out-of-range targets).  A
genuine `O(1)`-per-vertex generator: it never inspects all of `Fin n`. -/
def nbrsN (n : ℕ) (i : Fin n) : List (Fin n) :=
  [i.val + 1, i.val + 2, i.val + 3].filterMap
    (fun m => if h : m < n then some (⟨m, h⟩ : Fin n) else none)

/-- The sparse neighbour list is a sublist of `List.finRange n`. -/
theorem nbrsN_sublist_finRange (n : ℕ) (i : Fin n) :
    (nbrsN n i).Sublist (List.finRange n) := by
  unfold nbrsN
  simp +decide [ List.filterMap_cons, List.finRange ]
  split_ifs <;> simp +decide [ * ]
  · simp +decide [ List.ofFn_eq_map ]
    convert List.Sublist.trans ?_ ( List.take_sublist ( i + 1 + 3 ) ( List.finRange n ) ) using 1
    simp +arith +decide [ List.take_add_one ]
    simp +arith +decide [ * ]
  · rw [ List.ofFn_eq_map ]
    rw [ ← List.take_append_drop ( i + 1 ) ( List.finRange n ), List.map_append ]
    rw [ show ( List.drop ( i + 1 ) ( List.finRange n ) ) = [ ⟨ i + 1, by linarith ⟩, ⟨ i + 2, by linarith ⟩ ] from ?_ ] ; simp +decide
    refine' List.ext_get _ _ <;> simp +decide
    · omega
    · intro n hn hn'; interval_cases n <;> simp +decide
  · linarith
  · linarith

/-- Build a `NatGraphWithGenerator (Fin n)` from `nbrsN` (unit edge weights), with adjacency =
membership in the neighbour list.  `neighbours_sublist` is discharged by the size-independent
`toList_univ_finEnum_eq_finRange`, so this is cheap to elaborate for any `n`. -/
def sparseGraph (n : ℕ) : NatGraphWithGenerator (Fin n) where
  Adj u v := v ∈ nbrsN n u
  Payload _ _ _ := 1
  instDecAdj u v := inferInstanceAs (Decidable (v ∈ nbrsN n u))
  neighbours := nbrsN n
  neighbours_are_adj _ _ := Iff.rfl
  neighbours_sublist u := by
    rw [toList_univ_finEnum_eq_finRange n]; exact nbrsN_sublist_finRange n u

/-- Time forcing the boolean `r` (already computed by the caller), print `label` with the
elapsed time in microseconds, and return the clock for the next measurement. -/
def timeStep (label : String) (r : Bool) (t0 : Nat) : IO Nat := do
  let t1 ← IO.monoNanosNow
  IO.println s!"  {label}: found={r}, {(t1 - t0) / 1000} µs"
  (← IO.getStdout).flush
  IO.monoNanosNow

/-- Experiment 1: fixed vertex set (`|V| = 64`), increasing number of expanded nodes (the goal
moves away from the start).  Both algorithms slow down with the number of expansions — a
limitation of the shared functional search state. -/
def expandScaling : IO Unit := do
  let g : NatGraphWithGenerator (Fin 64) := sparseGraph 64
  IO.println "== Experiment 1: |V| = 64, increasing #expanded nodes (goal index) =="
  for goal in [3, 6, 9, 12] do
    let gg : Fin 64 := ⟨goal % 64, Nat.mod_lt _ (by norm_num)⟩
    let mut t ← IO.monoNanosNow
    t ← timeStep s!"orig goal={goal}" (foundPath (dijkstra (g := g.toWeightedDiGraph) ⟨0, by norm_num⟩ gg)) t
    let _ ← timeStep s!"gen  goal={goal}" (foundPath (dijkstra_gen g ⟨0, by norm_num⟩ gg)) t

/-- Experiment 2: the goal is fixed close to the start (`goal = 6`, ≈ 3 nodes expanded) while
`|V|` grows.  `dijkstra_gen` stays flat (cost depends only on the expanded frontier). -/
def vertexScaling : IO Unit := do
  let g16 : NatGraphWithGenerator (Fin 16) := sparseGraph 16
  let g32 : NatGraphWithGenerator (Fin 32) := sparseGraph 32
  let g48 : NatGraphWithGenerator (Fin 48) := sparseGraph 48
  let g64 : NatGraphWithGenerator (Fin 64) := sparseGraph 64
  IO.println "== Experiment 2: goal=6 (~3 nodes expanded), growing |V| =="
  for gv in [6] do
    let mut t ← IO.monoNanosNow
    t ← timeStep "orig |V|=16" (foundPath (dijkstra (g := g16.toWeightedDiGraph) ⟨0, by norm_num⟩ ⟨gv % 16, Nat.mod_lt _ (by norm_num)⟩)) t
    t ← timeStep "orig |V|=32" (foundPath (dijkstra (g := g32.toWeightedDiGraph) ⟨0, by norm_num⟩ ⟨gv % 32, Nat.mod_lt _ (by norm_num)⟩)) t
    t ← timeStep "orig |V|=48" (foundPath (dijkstra (g := g48.toWeightedDiGraph) ⟨0, by norm_num⟩ ⟨gv % 48, Nat.mod_lt _ (by norm_num)⟩)) t
    t ← timeStep "orig |V|=64" (foundPath (dijkstra (g := g64.toWeightedDiGraph) ⟨0, by norm_num⟩ ⟨gv % 64, Nat.mod_lt _ (by norm_num)⟩)) t
    t ← timeStep "gen  |V|=16" (foundPath (dijkstra_gen g16 ⟨0, by norm_num⟩ ⟨gv % 16, Nat.mod_lt _ (by norm_num)⟩)) t
    t ← timeStep "gen  |V|=32" (foundPath (dijkstra_gen g32 ⟨0, by norm_num⟩ ⟨gv % 32, Nat.mod_lt _ (by norm_num)⟩)) t
    t ← timeStep "gen  |V|=48" (foundPath (dijkstra_gen g48 ⟨0, by norm_num⟩ ⟨gv % 48, Nat.mod_lt _ (by norm_num)⟩)) t
    let _ ← timeStep "gen  |V|=64" (foundPath (dijkstra_gen g64 ⟨0, by norm_num⟩ ⟨gv % 64, Nat.mod_lt _ (by norm_num)⟩)) t

/-- Non-branching neighbour function: `i ↦ [i+1]` (empty at the last vertex).  Out-degree is
exactly `1`, so a search frontier never grows beyond a single node. -/
def pathNbrs (n : ℕ) (i : Fin n) : List (Fin n) :=
  if h : i.val + 1 < n then [(⟨i.val + 1, h⟩ : Fin n)] else []

/-- The singleton successor is a sublist of `List.finRange n`. -/
theorem pathNbrs_sublist_finRange (n : ℕ) (i : Fin n) :
    (pathNbrs n i).Sublist (List.finRange n) := by
  unfold pathNbrs
  split
  · rw [List.singleton_sublist]; exact List.mem_finRange _
  · exact List.nil_sublist _

/-- A single directed path `0 → 1 → 2 → ⋯ → n-1` (unit edge weights) as a generator graph.
Every vertex has out-degree `1`, so the shortest path to vertex `k` is found after expanding
exactly `k` nodes, *independently of* `n`. -/
def pathGraph (n : ℕ) : NatGraphWithGenerator (Fin n) where
  Adj u v := v ∈ pathNbrs n u
  Payload _ _ _ := 1
  instDecAdj u v := inferInstanceAs (Decidable (v ∈ pathNbrs n u))
  neighbours := pathNbrs n
  neighbours_are_adj _ _ := Iff.rfl
  neighbours_sublist u := by
    rw [toList_univ_finEnum_eq_finRange n]; exact pathNbrs_sublist_finRange n u

/-- Time one generator search on the path graph `Fin n` from vertex `0` to `goal % n`.

`n` and `goal` are ordinary *run-time* arguments, so `pathGraph n` is **not** a closed term:
this is essential, because Lean lifts closed terms out of function bodies and evaluates them at
module initialisation (program startup).  A literal `pathGraph 50000` here would therefore make
the search run at startup instead of inside `main` (and, for the original billion-vertex
literals, hang the whole executable before it prints anything). -/
def timePathGen (label : String) (n : Nat) (hn : 0 < n) (goal : Nat) (t0 : Nat) : IO Nat :=
  timeStep label
    (foundPath (dijkstra_gen (pathGraph n) ⟨0, hn⟩ ⟨goal % n, Nat.mod_lt _ hn⟩)) t0

/-- Experiment 3: a non-branching path with the goal fixed at depth `100`, while `|V|` grows
all the way to one **billion** vertices.

Each search expands only ≈ 100 nodes (out-degree is `1`), and the end-to-end wall-clock time of
the full `dijkstra_gen` call is now **flat** in `|V|` (≈ 200 ms across `|V| = 10³ … 10⁹`).

This used to be `Θ(|V|²)` and crashed with a stack overflow beyond `|V| ≈ 6.5 × 10⁴`: the
verified core forced the well-founded termination metric `hsearch_termination_metric`, whose
type `Vector _ g.nodeNum` made the compiler evaluate `g.nodeNum = Fintype.card V` once per
call, and for a `FinEnum` graph that enumerates the whole vertex set (`FinEnum.toList (Fin n)`
is not stack-safe).  The generator algorithms now use `hsearch_termination_metric_nat`, a
metric valued in `ℕ × ℕ × ℕ × ℕ`, whose type mentions no `nodeNum`; since a termination metric
is only used inside the (erased) well-foundedness proof and never computed at run time,
nothing forces the vertex-set enumeration any more.  `dijkstra_gen`/`astar_gen` are still proved
equal to `dijkstra`/`astar` (`dijkstra_gen_eq`, `astar_gen_eq`), so all correctness results
transfer unchanged.

The *original* `dijkstra` is omitted: it scans **all** `|V|` vertices per expansion, so even one
expansion is `Θ(|V|)`. -/
def hugeGraph : IO Unit := do
  IO.println "== Experiment 3: non-branching path, goal at depth 100, growing |V| (generator only) =="
  IO.println "   (end-to-end dijkstra_gen; now flat in |V| — nodeNum-free termination metric)"
  let mut t ← IO.monoNanosNow
  t ← timePathGen "gen |V|=1000"        1000        (by norm_num) 100 t
  t ← timePathGen "gen |V|=1000000"     1000000     (by norm_num) 100 t
  t ← timePathGen "gen |V|=100000000"   100000000   (by norm_num) 100 t
  let _ ← timePathGen "gen |V|=1000000000" 1000000000 (by norm_num) 100 t

/-- Goal *predicate*: the vertex whose index equals `depth`.  Used by the generator-based
multi-goal searches, which take a decidable goal predicate rather than a fixed goal node. -/
def isGoalAt (n depth : ℕ) : Fin n → Prop := fun v => v.val = depth

instance (n depth : ℕ) : DecidablePred (isGoalAt n depth) := fun v => by
  unfold isGoalAt; infer_instance

/-- Admissible A* heuristic towards `isGoalAt n depth` on the non-branching path graph: the
remaining number of unit-cost edges `depth - v` (truncated `Nat` subtraction). -/
def heurTo (n depth : ℕ) : Fin n → ℕ∞ := fun v => ((depth - v.val : ℕ) : ℕ∞)

/-- Time one generator-based *multi-goal* search (goal given by the predicate `isGoalAt n
depth`) for both `dijkstra_multigoal_gen` and `astar_multigoal_gen` on the path graph `Fin n`
from vertex `0`.  As in Experiment 3, `n` is a run-time argument so the search stays inside
`main`. -/
def timeMultiGen (label : String) (n : Nat) (hn : 0 < n) (depth : Nat) : IO Unit := do
  let t0 ← IO.monoNanosNow
  let rd := foundPath (dijkstra_multigoal_gen (pathGraph n) ⟨0, hn⟩ (isGoalAt n depth))
  let t1 ← IO.monoNanosNow
  let ra := foundPath (astar_multigoal_gen (pathGraph n) (heurTo n depth) ⟨0, hn⟩ (isGoalAt n depth))
  let t2 ← IO.monoNanosNow
  IO.println s!"  {label}: dijkstra found={rd}, {(t1 - t0) / 1000} µs   astar found={ra}, {(t2 - t1) / 1000} µs"
  (← IO.getStdout).flush

/-- Experiment 4: generator-based **multi-goal** search driven by a goal *predicate*
(`isGoalAt`), for both `dijkstra_multigoal_gen` and `astar_multigoal_gen`, on a non-branching
path with the (single) goal fixed at depth `100`, while `|V|` grows to one hundred **million**
vertices.

The multi-goal searches reduce to a single-goal `astar_gen`/`dijkstra_gen` on the augmented
graph `add_artificial_goal_gen` over `Option (Fin n)`: a fresh sink `none` is connected (by
the generator) to exactly the nodes satisfying the predicate, and the search runs towards
`none`.  Because the augmentation reuses the neighbour generator and the `nodeNum`-free
termination metric, the end-to-end time is again **flat** in `|V|` (measured ≈ 320 ms across
`|V| = 10³ … 10⁸`, dominated by the ≈100 expanded nodes), and all correctness results transfer
via `astar_multigoal_gen_eq` (soundness, completeness, optimality). -/
def multiGoalScaling : IO Unit := do
  IO.println "== Experiment 4: generator multi-goal (goal predicate), goal at depth 100, growing |V| =="
  IO.println "   (dijkstra_multigoal_gen & astar_multigoal_gen; flat in |V|)"
  timeMultiGen "|V|=1000"      1000      (by norm_num) 100
  timeMultiGen "|V|=100000"    100000    (by norm_num) 100
  timeMultiGen "|V|=1000000"   1000000   (by norm_num) 100
  timeMultiGen "|V|=100000000" 100000000 (by norm_num) 100

def main : IO Unit := do
  expandScaling
  IO.println ""
  vertexScaling
  IO.println ""
  hugeGraph
  IO.println ""
  multiGoalScaling
