import SearchAlgorithms.DijkstraFast
import SearchAlgorithms.DijkstraSorted
import SearchAlgorithms.DijkstraMap
import BenchAux

/-!
# Benchmark: a search with a *large* queue

The "path graph" benchmarks of `Bench` keep the search queue at size ≤ 1, so they only
measure the cost of the visited set and of the path-order/mother lookups.  This file adds a
graph on which the queue becomes as large as the vertex set:

* vertex `0` is connected to **all** other vertices (with edge cost `v + 1`),
* every other vertex has no outgoing edge.

The first expansion therefore puts `n - 1` nodes into the queue, and every later expansion
pops one node and produces no new ones.  With a queue that is re-sorted from scratch on every
expansion this costs `Θ(n² log n)` comparisons in total; a queue that is kept sorted only
needs to re-`merge` the (empty) list of new nodes, i.e. `O(1)` per step.

Measured (`lake exe benchbroom`):

| `|V|` | `dijkstra_fast` | `dijkstra_sorted` |
|-------|-----------------|-------------------|
| 250   | 19 ms           | 0.5 ms            |
| 500   | 60 ms           | 2.2 ms            |
| 1000  | 269 ms          | 2.4 ms            |
| 2000  | 1335 ms         | 2.6 ms            |
| 4000  | —               | 9.8 ms            |
-/

open WeightedDiGraph NatGraph

/-- Neighbours of the broom graph: vertex `0` sees everybody else, all other vertices are
sinks. -/
def broomNbrs (n : ℕ) (i : Fin n) : List (Fin n) :=
  if i.val = 0 then (List.finRange n).drop 1 else []

theorem broomNbrs_sublist_finRange (n : ℕ) (i : Fin n) :
    (broomNbrs n i).Sublist (List.finRange n) := by
  unfold broomNbrs
  split
  · exact List.drop_sublist 1 _
  · exact List.nil_sublist _

/-- The broom graph: `0 → v` for every `v ≠ 0`, with edge cost `v + 1`. -/
def broomGraph (n : ℕ) : NatGraphWithGenerator (Fin n) where
  Adj u v := v ∈ broomNbrs n u
  Payload _ v _ := v.val + 1
  instDecAdj u v := inferInstanceAs (Decidable (v ∈ broomNbrs n u))
  neighbours := broomNbrs n
  neighbours_are_adj _ _ := Iff.rfl
  neighbours_sublist u := by
    rw [toList_univ_finEnum_eq_finRange n]; exact broomNbrs_sublist_finRange n u

@[inline] def foundPath' {α : Type} : Option α → Bool
  | some _ => true
  | none   => false

/-- Time the fast (hash-set) implementation on the broom graph with `n` vertices, searching
for the most expensive vertex (so that the whole queue is consumed). -/
def timeBroomFast (n : Nat) (hn : 1 < n) : IO Unit := do
  let t0 ← IO.monoNanosNow
  let r := foundPath' (dijkstra_fast (broomGraph n) ⟨0, by omega⟩ ⟨n - 1, by omega⟩)
  let t1 ← IO.monoNanosNow
  IO.println s!"  broom fast |V|={n}: found={r}, {(t1 - t0) / 1000} µs"
  (← IO.getStdout).flush

/-- Time the sorted-queue implementation on the broom graph with `n` vertices. -/
def timeBroomSorted (n : Nat) (hn : 1 < n) : IO Unit := do
  let t0 ← IO.monoNanosNow
  let r := foundPath' (dijkstra_sorted (broomGraph n) ⟨0, by omega⟩ ⟨n - 1, by omega⟩)
  let t1 ← IO.monoNanosNow
  IO.println s!"  broom sorted |V|={n}: found={r}, {(t1 - t0) / 1000} µs"
  (← IO.getStdout).flush

def main : IO Unit := do
  IO.println "== broom graph (queue of size |V|-1, one pop per step) =="
  timeBroomFast 250 (by norm_num)
  timeBroomFast 500 (by norm_num)
  timeBroomFast 1000 (by norm_num)
  timeBroomFast 2000 (by norm_num)
  timeBroomSorted 250 (by norm_num)
  timeBroomSorted 500 (by norm_num)
  timeBroomSorted 1000 (by norm_num)
  timeBroomSorted 2000 (by norm_num)
  timeBroomSorted 4000 (by norm_num)
