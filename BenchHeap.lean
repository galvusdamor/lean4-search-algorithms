import SearchAlgorithms.DijkstraSorted
import SearchAlgorithms.DijkstraHeap
import BenchAux

/-!
# Benchmark: sorted list versus heap as search queue

`BenchHuge` showed that the remaining super-linear cost of `dijkstra_sorted` is the *insertion*
into the queue: the queue is a sorted list, so putting a node at position `k` copies `k`
cells.  A search whose queue keeps growing (the binary tree below) therefore costs
`Θ(queue length)` per expansion.

`SearchAlgorithms.DijkstraHeap` replaces the list by a leftist heap, where an insertion is
`O(log m)` and shares the rest of the heap.  This file runs the two implementations on the
same graphs.  They are *proved* to return the same path (`dijkstra_heap_eq_sorted`), so only
the run time can differ.

Two graph families, as in `BenchHuge`:

* **`tree n`** — the complete binary tree `i → 2i+1, 2i+2` with edge costs `(v % 5) + 1`: the
  queue grows to `Θ(n)` and is written to in every expansion.  This is the case the heap is
  meant to fix.
* **`broom n`** — vertex `0` is connected to all others (edge cost `v + 1`), everything else
  is a sink: the queue is filled once with `n - 1` nodes and then drained.  Here the sorted
  list is already linear, and the heap has to pay `n` `merge`s instead; the run shows what
  that costs.

Usage:

```
lake exe benchheap               -- the standard suite
lake exe benchheap tree 40000    -- one tree run with both implementations
lake exe benchheap treeheap 40000 -- only the heap on the tree
lake exe benchheap broom 100000  -- one broom run with both implementations
lake exe benchheap micro 1000000 -- the heap data structure alone
```

The output of a run is recorded in `bench-results-heap.txt`, and the README summarises it:
on the tree the heap is ~80× faster at `|V| = 40000` and removes the quadratic behaviour; on
the broom it is ~5–8× slower, because there the sorted list never pays for an insertion in
the middle.

The sizes are run-time arguments on purpose: a *closed* search expression is lifted by the
compiler and evaluated at module initialisation, i.e. outside the timed region.
-/

open WeightedDiGraph NatGraph

/-! ## The graphs -/

/-- Neighbours of the broom graph: vertex `0` sees everybody else, all other vertices are
sinks. -/
def heapBroomNbrs (n : ℕ) (i : Fin n) : List (Fin n) :=
  if i.val = 0 then (List.finRange n).drop 1 else []

theorem heapBroomNbrs_sublist (n : ℕ) (i : Fin n) :
    (heapBroomNbrs n i).Sublist (List.finRange n) := by
  unfold heapBroomNbrs
  split
  · exact List.drop_sublist 1 _
  · exact List.nil_sublist _

/-- The broom graph: `0 → v` for every `v ≠ 0`, with edge cost `v + 1`. -/
def heapBroomGraph (n : ℕ) : NatGraphWithGenerator (Fin n) where
  Adj u v := v ∈ heapBroomNbrs n u
  Payload _ v _ := v.val + 1
  instDecAdj u v := inferInstanceAs (Decidable (v ∈ heapBroomNbrs n u))
  neighbours := heapBroomNbrs n
  neighbours_are_adj _ _ := Iff.rfl
  neighbours_sublist u := by
    rw [toList_univ_finEnum_eq_finRange n]; exact heapBroomNbrs_sublist n u

/-- Neighbours in the complete binary tree on `Fin n`: the children `2i+1`, `2i+2`. -/
def heapTreeNbrs (n : ℕ) (i : Fin n) : List (Fin n) :=
  if h1 : 2 * i.val + 1 < n then
    if h2 : 2 * i.val + 2 < n then [⟨2 * i.val + 1, h1⟩, ⟨2 * i.val + 2, h2⟩]
    else [⟨2 * i.val + 1, h1⟩]
  else []

theorem heapTreeNbrs_pairwise_lt (n : ℕ) (i : Fin n) :
    (heapTreeNbrs n i).Pairwise (· < ·) := by
  unfold heapTreeNbrs
  split
  · split
    · refine List.pairwise_cons.mpr ⟨?_, List.pairwise_singleton _ _⟩
      intro b hb
      rw [List.mem_singleton] at hb
      subst hb
      exact Fin.mk_lt_mk.mpr (by omega)
    · exact List.pairwise_singleton _ _
  · exact List.Pairwise.nil

/-- The binary-tree graph, with edge costs `(v % 5) + 1` so that the newly queued nodes end up
at data-dependent positions of the queue. -/
def heapTreeGraph (n : ℕ) : NatGraphWithGenerator (Fin n) where
  Adj u v := v ∈ heapTreeNbrs n u
  Payload _ v _ := v.val % 5 + 1
  instDecAdj u v := inferInstanceAs (Decidable (v ∈ heapTreeNbrs n u))
  neighbours := heapTreeNbrs n
  neighbours_are_adj _ _ := Iff.rfl
  neighbours_sublist u := by
    rw [toList_univ_finEnum_eq_finRange n]
    exact sublist_finRange_of_pairwise_lt _ (heapTreeNbrs_pairwise_lt n u)

/-! ## Timing helpers -/

/-- Whether a search returned a path (a plain constructor `match`). -/
@[inline] def heapFound {α : Type} : Option α → Bool
  | some _ => true
  | none => false

def heapReport (label : String) (found : Bool) (t0 t1 : Nat) (steps : Nat) : IO Unit := do
  let us := (t1 - t0) / 1000
  let per := if steps = 0 then 0 else (t1 - t0) / steps
  IO.println s!"  {label}: found={found}, {us / 1000} ms ({us} µs), ~{steps} expansions, \
{per} ns/expansion"
  (← IO.getStdout).flush

/-! ## The individual experiments -/

/-- Binary tree with `n` vertices, goal = the last vertex, with the sorted-list queue. -/
def runTreeSortedQ (n : Nat) : IO Unit := do
  if h : 1 < n then
    let t0 ← IO.monoNanosNow
    let r := heapFound (dijkstra_sorted (heapTreeGraph n) ⟨0, by omega⟩ ⟨n - 1, by omega⟩)
    let t1 ← IO.monoNanosNow
    heapReport s!"tree  sorted |V|={n}" r t0 t1 n
  else IO.println "  (need |V| > 1)"

/-- Binary tree with `n` vertices, goal = the last vertex, with the heap queue. -/
def runTreeHeapQ (n : Nat) : IO Unit := do
  if h : 1 < n then
    let t0 ← IO.monoNanosNow
    let r := heapFound (dijkstra_heap (heapTreeGraph n) ⟨0, by omega⟩ ⟨n - 1, by omega⟩)
    let t1 ← IO.monoNanosNow
    heapReport s!"tree  heap   |V|={n}" r t0 t1 n
  else IO.println "  (need |V| > 1)"

/-- Broom with `n` vertices, whole queue drained, with the sorted-list queue. -/
def runBroomSortedQ (n : Nat) : IO Unit := do
  if h : 1 < n then
    let t0 ← IO.monoNanosNow
    let r := heapFound (dijkstra_sorted (heapBroomGraph n) ⟨0, by omega⟩ ⟨n - 1, by omega⟩)
    let t1 ← IO.monoNanosNow
    heapReport s!"broom sorted |V|={n}" r t0 t1 n
  else IO.println "  (need |V| > 1)"

/-- Broom with `n` vertices, whole queue drained, with the heap queue. -/
def runBroomHeapQ (n : Nat) : IO Unit := do
  if h : 1 < n then
    let t0 ← IO.monoNanosNow
    let r := heapFound (dijkstra_heap (heapBroomGraph n) ⟨0, by omega⟩ ⟨n - 1, by omega⟩)
    let t1 ← IO.monoNanosNow
    heapReport s!"broom heap   |V|={n}" r t0 t1 n
  else IO.println "  (need |V| > 1)"

/-- Micro-benchmark of the heap itself: build a heap of `n` numbers and pop them all, with a
comparator that is a single `Nat` comparison.  This separates the cost of the data structure
from the cost of the search's comparator (two hash-map lookups and `ℕ∞` arithmetic). -/
def runHeapMicro (n : Nat) : IO Unit := do
  let t0 ← IO.monoNanosNow
  let h := SearchAlgorithms.LHeap.ofList (fun a b : Nat × Nat => a.1 ≤ b.1)
    ((List.range n).map (fun i => (i * 7919 % n, i)))
  let rec drain (fuel : Nat) (h : SearchAlgorithms.LHeap (Nat × Nat)) (acc : Nat) : Nat :=
    match fuel with
    | 0 => acc
    | fuel + 1 =>
      match h.peek with
      | none => acc
      | some x => drain fuel
          (SearchAlgorithms.LHeap.deleteMin (fun a b : Nat × Nat => a.1 ≤ b.1) h) (acc + x.1)
  -- store the result in a reference: passing it to a function forces its evaluation, so the
  -- work really happens inside the timed region
  let ref ← IO.mkRef 0
  ref.set (drain n h 0)
  let t1 ← IO.monoNanosNow
  let r ← ref.get
  heapReport s!"heap  micro  n={n} (checksum {r % 1000})" true t0 t1 n

def heapSuite : IO Unit := do
  IO.println "== binary tree: the queue grows throughout the search =="
  runTreeSortedQ 10000
  runTreeHeapQ 10000
  runTreeSortedQ 20000
  runTreeHeapQ 20000
  runTreeSortedQ 40000
  runTreeHeapQ 40000
  runTreeHeapQ 160000
  IO.println "== broom: the queue is filled once and then drained =="
  runBroomSortedQ 100000
  runBroomHeapQ 100000
  runBroomSortedQ 1000000
  runBroomHeapQ 1000000

def main (args : List String) : IO Unit := do
  match args with
  | ["tree", n] => do runTreeSortedQ (n.toNat!); runTreeHeapQ (n.toNat!)
  | ["treeheap", n] => runTreeHeapQ (n.toNat!)
  | ["micro", n] => runHeapMicro (n.toNat!)
  | ["broom", n] => do runBroomSortedQ (n.toNat!); runBroomHeapQ (n.toNat!)
  | _ => heapSuite
