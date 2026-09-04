import SearchAlgorithms.AStarHeapLazyPath
import SearchAlgorithms.AStarSortedPath
import SearchAlgorithms.DijkstraHeapLazy
import SearchAlgorithms.DijkstraSorted
import BenchAux

/-!
# Benchmark: path reconstruction

Every search in this library rebuilds the answer from the mother pointers with
`WeightedDiGraph.extract_path_to`, which appends one edge at the *end* of the path built so
far and is therefore `Θ(L²)` in the length `L` of the returned path.  On the searches whose
per-expansion cost is now flat (`SearchAlgorithms.HeapLazyState`), this reconstruction is what
dominates a run whose answer is long.

`SearchAlgorithms.ExtractPathFast` reconstructs the same path in `O(L)` by growing the walk at
its front, and `SearchAlgorithms.AStarHeapLazyPath` runs the lazy-heap searches with it.  This
benchmark compares the two on graphs whose answer is a path through (almost) every vertex:

* **`chain n`** — the chain-broom of `BenchHeapLazy`: vertex `0` is connected to every other
  vertex (cost `5v`) and `i` to `i + 1` (cost `1`), so the cheapest path to `n-1` is the whole
  chain and `L = n - 1`.  Expanding `0` fills the queue, every later expansion is a
  decrease-key.
* **`path n`** — the plain path `0 → 1 → ⋯ → n-1`: the queue never holds more than one node,
  so essentially *all* of the time is start-up plus reconstruction.

Both searches are proved to return the same path
(`NatGraph.astar_heap_lazy_fastpath_eq_lazy`), so only the run time can differ.

```
lake exe benchpath                 -- the standard suite
lake exe benchpath chain 32000     -- one chain-broom run with both reconstructions
lake exe benchpath path 32000      -- one path run with both reconstructions
lake exe benchpath sorted 32000    -- the same on the maintained sorted queue
lake exe benchpath pathnew 256000  -- only the linear reconstruction, at a large size
```

## Measured (8-core x86-64 Linux, full output in `bench-results-path.txt`)

Wall-clock time of the whole call, Dijkstra with the lazily deleted heap:

| graph, `|V|` | `extract_path_to` | `extract_path_fast` |
|-------------:|------------------:|--------------------:|
| path  8000   |            171 ms |               10 ms |
| path  16000  |            625 ms |               18 ms |
| path  32000  |           3063 ms |               69 ms |
| chain 8000   |            274 ms |              130 ms |
| chain 16000  |            921 ms |              158 ms |
| chain 32000  |           3270 ms |              332 ms |

The old times quadruple per doubling (`Θ(L²)`), the new ones double.  With the maintained
sorted queue instead of the heap the picture is the same (plain path, `|V| = 32000`:
3006 ms → 56 ms).  At sizes the quadratic reconstruction cannot reach any more, the linear
one stays linear: plain path 64000 / 128000 / 256000 in 105 / 267 / 537 ms, chain-broom in
0.7 / 1.4 / 3.8 s.

On the chain-broom the time that is left after the change is the *search* (the queue holds
`|V| - i` nodes throughout); on the plain path it is start-up plus the reconstruction.

Note on the measurement: the timed value is bound with `IO.lazyPure`, which forces it inside
the timed region.  A plain `let` in a `do` block would be evaluated when the result is first
used — after the second clock reading — and every run would be reported as 0 µs.
-/

open WeightedDiGraph NatGraph

/-! ## The graphs -/

/-- Neighbours of the chain-broom: vertex `0` sees every other vertex, `i ≠ 0` sees `i+1`. -/
def bpChainNbrs (n : ℕ) (i : Fin n) : List (Fin n) :=
  if i.val = 0 then (List.finRange n).drop 1
  else if h : i.val + 1 < n then [⟨i.val + 1, h⟩] else []

theorem bpChainNbrs_sublist (n : ℕ) (i : Fin n) :
    (bpChainNbrs n i).Sublist (List.finRange n) := by
  unfold bpChainNbrs
  split
  · exact List.drop_sublist 1 _
  · split
    · exact sublist_finRange_of_pairwise_lt _ (List.pairwise_singleton _ _)
    · exact List.nil_sublist _

/-- The chain-broom: the answer is the whole chain, so the returned path has `n-1` edges. -/
def bpChainGraph (n : ℕ) : NatGraphWithGenerator (Fin n) where
  Adj u v := v ∈ bpChainNbrs n u
  Payload u v _ := if u.val = 0 then 5 * v.val else 1
  instDecAdj u v := inferInstanceAs (Decidable (v ∈ bpChainNbrs n u))
  neighbours := bpChainNbrs n
  neighbours_are_adj _ _ := Iff.rfl
  neighbours_sublist u := by
    rw [toList_univ_finEnum_eq_finRange n]
    exact bpChainNbrs_sublist n u

/-- Neighbours in the plain path `0 → 1 → … → n-1`. -/
def bpPathNbrs (n : ℕ) (i : Fin n) : List (Fin n) :=
  if h : i.val + 1 < n then [⟨i.val + 1, h⟩] else []

theorem bpPathNbrs_pairwise_lt (n : ℕ) (i : Fin n) :
    (bpPathNbrs n i).Pairwise (· < ·) := by
  unfold bpPathNbrs
  split
  · exact List.pairwise_singleton _ _
  · exact List.Pairwise.nil

/-- The plain path graph: the queue never holds more than one node. -/
def bpPathGraph (n : ℕ) : NatGraphWithGenerator (Fin n) where
  Adj u v := v ∈ bpPathNbrs n u
  Payload _ v _ := v.val % 5 + 1
  instDecAdj u v := inferInstanceAs (Decidable (v ∈ bpPathNbrs n u))
  neighbours := bpPathNbrs n
  neighbours_are_adj _ _ := Iff.rfl
  neighbours_sublist u := by
    rw [toList_univ_finEnum_eq_finRange n]
    exact sublist_finRange_of_pairwise_lt _ (bpPathNbrs_pairwise_lt n u)

/-! ## Timing helpers -/

/-- The number of edges of the returned path, `0` if none was found.  Traversing the walk
forces the whole reconstruction. -/
def bpLength {V E : Type} [FinEnum V] {G : WeightedDiGraph V E} {u v : V} :
    Option (G.Path u v) → Nat
  | some p => p.val.length
  | none => 0

def bpReport (label : String) (len : Nat) (t0 t1 : Nat) : IO Unit := do
  let us := (t1 - t0) / 1000
  IO.println s!"  {label}: |path|={len}, {us / 1000} ms ({us} µs)"
  (← IO.getStdout).flush

/-! ## The individual experiments -/

/-- Chain-broom, lazily deleted heap, quadratic reconstruction (`extract_path_to`). -/
def runChainOld (n : Nat) : IO Unit := do
  if h : 1 < n then
    let t0 ← IO.monoNanosNow
    let l ← IO.lazyPure (fun _ =>
      bpLength (dijkstra_heap_lazy (bpChainGraph n) ⟨0, by omega⟩ ⟨n - 1, by omega⟩ 0))
    let t1 ← IO.monoNanosNow
    bpReport s!"chain extract_path_to   |V|={n}" l t0 t1
  else IO.println "  (need |V| > 1)"

/-- Chain-broom, lazily deleted heap, linear reconstruction (`extract_path_fast`). -/
def runChainNew (n : Nat) : IO Unit := do
  if h : 1 < n then
    let t0 ← IO.monoNanosNow
    let l ← IO.lazyPure (fun _ =>
      bpLength (dijkstra_heap_lazy_fastpath (bpChainGraph n) ⟨0, by omega⟩ ⟨n - 1, by omega⟩ 0))
    let t1 ← IO.monoNanosNow
    bpReport s!"chain extract_path_fast |V|={n}" l t0 t1
  else IO.println "  (need |V| > 1)"

/-- Plain path, lazily deleted heap, quadratic reconstruction. -/
def runPathOld (n : Nat) : IO Unit := do
  if h : 1 < n then
    let t0 ← IO.monoNanosNow
    let l ← IO.lazyPure (fun _ =>
      bpLength (dijkstra_heap_lazy (bpPathGraph n) ⟨0, by omega⟩ ⟨n - 1, by omega⟩ 0))
    let t1 ← IO.monoNanosNow
    bpReport s!"path  extract_path_to   |V|={n}" l t0 t1
  else IO.println "  (need |V| > 1)"

/-- Plain path, lazily deleted heap, linear reconstruction. -/
def runPathNew (n : Nat) : IO Unit := do
  if h : 1 < n then
    let t0 ← IO.monoNanosNow
    let l ← IO.lazyPure (fun _ =>
      bpLength (dijkstra_heap_lazy_fastpath (bpPathGraph n) ⟨0, by omega⟩ ⟨n - 1, by omega⟩ 0))
    let t1 ← IO.monoNanosNow
    bpReport s!"path  extract_path_fast |V|={n}" l t0 t1
  else IO.println "  (need |V| > 1)"

/-- Plain path, maintained sorted queue, quadratic reconstruction. -/
def runSortedOld (n : Nat) : IO Unit := do
  if h : 1 < n then
    let t0 ← IO.monoNanosNow
    let l ← IO.lazyPure (fun _ =>
      bpLength (dijkstra_sorted (bpPathGraph n) ⟨0, by omega⟩ ⟨n - 1, by omega⟩))
    let t1 ← IO.monoNanosNow
    bpReport s!"sortd extract_path_to   |V|={n}" l t0 t1
  else IO.println "  (need |V| > 1)"

/-- Plain path, maintained sorted queue, linear reconstruction. -/
def runSortedNew (n : Nat) : IO Unit := do
  if h : 1 < n then
    let t0 ← IO.monoNanosNow
    let l ← IO.lazyPure (fun _ =>
      bpLength (dijkstra_sorted_fastpath (bpPathGraph n) ⟨0, by omega⟩ ⟨n - 1, by omega⟩))
    let t1 ← IO.monoNanosNow
    bpReport s!"sortd extract_path_fast |V|={n}" l t0 t1
  else IO.println "  (need |V| > 1)"

def bpSuite : IO Unit := do
  IO.println "== plain path: the answer is the whole graph, the queue is trivial =="
  runPathOld 8000
  runPathNew 8000
  runPathOld 16000
  runPathNew 16000
  runPathOld 32000
  runPathNew 32000
  IO.println "== chain-broom: a decrease-key in every expansion, answer = whole chain =="
  runChainOld 8000
  runChainNew 8000
  runChainOld 16000
  runChainNew 16000
  runChainOld 32000
  runChainNew 32000
  IO.println "== plain path with the maintained sorted queue instead of the lazy heap =="
  runSortedOld 16000
  runSortedNew 16000
  runSortedOld 32000
  runSortedNew 32000

def main (args : List String) : IO Unit := do
  match args with
  | ["chain", n] => do runChainOld n.toNat!; runChainNew n.toNat!
  | ["chainold", n] => runChainOld n.toNat!
  | ["chainnew", n] => runChainNew n.toNat!
  | ["path", n] => do runPathOld n.toNat!; runPathNew n.toNat!
  | ["pathold", n] => runPathOld n.toNat!
  | ["pathnew", n] => runPathNew n.toNat!
  | ["sorted", n] => do runSortedOld n.toNat!; runSortedNew n.toNat!
  | ["sortedold", n] => runSortedOld n.toNat!
  | ["sortednew", n] => runSortedNew n.toNat!
  | _ => bpSuite
