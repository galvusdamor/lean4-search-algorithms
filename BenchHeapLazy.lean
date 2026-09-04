import SearchAlgorithms.DijkstraHeap
import SearchAlgorithms.DijkstraSorted
import SearchAlgorithms.DijkstraFast
import SearchAlgorithms.DijkstraHeapLazy
import BenchAux

/-!
# Benchmark: eagerly updated heap versus lazily deleted heap

`SearchAlgorithms.HeuristicSearchHeap` keeps the queue in a leftist heap ordered by the
*current* path order.  When an expansion improves the path order of a node that is still in
the queue (a **decrease-key**), the comparison function changes, the heap invariant may break
and the whole queue is rebuilt — `Θ(m log m)` for a queue of `m` nodes.

`SearchAlgorithms.HeapLazyState` stores in every entry the path order it was queued with, so
the comparison function never changes; a decrease-key inserts a new entry and leaves the old
one behind as a *stale* entry, which is dropped when it reaches the root.  Every expansion is
then `O(deg · log m)`.

The two implementations are *proved* to return the same path
(`dijkstra_heap_lazy_eq_heap`), so only the run time can differ.

Graph families:

* **`grid n`** — the `n × n` grid with edges to the right and downward neighbour and
  data-dependent edge costs.  Every vertex is reached along two different routes, so
  decrease-keys happen all the time — but the queue stays small (the frontier of the grid).
* **`tree n`** — the complete binary tree of `BenchHeap`, where every vertex has exactly one
  predecessor and *no* decrease-key ever happens.  It shows what the lazy book-keeping costs
  when it does not pay off.
* **`chain n`** — the *chain-broom*: vertex `0` is connected to every other vertex (edge cost
  `5v`), and `i` is connected to `i + 1` (cost `1`).  Expanding `0` fills the queue with
  `|V| - 1` nodes and every later expansion improves the path order of a node that is still
  in that queue: a decrease-key on a **large** queue in every single expansion.  This is the
  case the lazy heap is meant to fix.
* **`chainflat n`** and **`split n`** — two controls for the chain-broom.  `chainflat` has the
  same shape but an expensive chain edge, so nothing is ever re-queued; `split` queues a
  *new* node in every expansion instead of re-queueing one.

Usage:

```
lake exe benchlazy                 -- the standard suite
lake exe benchlazy grid 300        -- one 300×300 grid run with both implementations
lake exe benchlazy gridlazy 300    -- only the lazy heap on the grid
lake exe benchlazy tree 40000      -- one tree run with both implementations
lake exe benchlazy chain 4000      -- chain-broom with both heap implementations
lake exe benchlazy chainsorted 4000-- chain-broom with the sorted-list queue
lake exe benchlazy chainflat 16000 -- the control without decrease-keys
lake exe benchlazy split 16000     -- the control that queues a new node instead
lake exe benchlazy chaintrace 16000-- the lazy heap on the chain-broom, tracing every 1000 nodes
lake exe benchlazy chaintrace 32000 20 -- ... tracing every 20 nodes
lake exe benchlazy flattrace 32000 20  -- the same for the control without decrease-keys
lake exe benchlazy trace 200       -- the lazy heap on a 200×200 grid, tracing every 1000 nodes
```

## Measured (8-core x86-64 Linux, full output in `bench-results-lazy.txt`)

**Chain-broom** — a decrease-key on a queue of almost `|V|` nodes in every expansion.  This
is where the three queue representations differ by orders of magnitude:

| `|V|` | sorted list | eager heap | lazy heap |
|------:|------------:|-----------:|----------:|
| 2000  |      1524 ms|    6283 ms |     21 ms |
| 4000  |           — |   30858 ms |    109 ms |
| 16000 |           — |          — |    900 ms |

The eager heap has to rebuild the queue whenever a queued node changes its path order, which
is `Θ(m log m)` per expansion; the lazy heap inserts a second entry for the node and drops
the obsolete one when it reaches the root.

**Grid** (small queue) and **binary tree** (no decrease-key): both heaps are within noise of
each other, 3–4 µs per expansion on the grid and 7–10 µs on the tree, so the lazy
book-keeping costs nothing measurable when it does not pay off.

**Where the remaining chain-broom time goes — not into the queue.**  `chaintrace n every`
and `flattrace n every` print a progress line every `every` expansions.  Timestamping those
lines splits a run into three phases (start-up and the expansion of vertex `0`, which queues
all `|V| - 1` others; the remaining expansions; and everything that happens *after* the last
expansion):

| graph, `|V|` | start-up + first 1000 | expansions | µs/expansion | after the search |
|-------------:|----------------------:|-----------:|--------------:|-----------------:|
| chain 8000   |                394 ms |      11 ms |           1.4 |           184 ms |
| chain 16000  |                292 ms |      65 ms |           4.0 |           666 ms |
| chain 32000  |                390 ms |     177 ms |           5.5 |          2846 ms |
| flat  8000   |                362 ms |      40 ms |           5.0 |             4 ms |
| flat  16000  |                467 ms |      97 ms |           6.1 |             5 ms |
| flat  32000  |                697 ms |     309 ms |           9.6 |             4 ms |

The search itself is a few microseconds per expansion and does not get slower as the queue
fills up — with *or* without decrease-keys.  What costs seconds on the chain-broom happens
**after** the last expansion: `WeightedDiGraph.extract_path_to` rebuilds the path from the
mother pointers by appending one edge at the *end* of the path built so far (`Walk.concat`,
which is `Walk.append` of the whole prefix), so reconstructing a path with `L` edges is
`Θ(L²)`.  The chain-broom's answer *is* the whole chain `0 → 1 → ⋯ → n-1`, i.e. `L = |V|-1`,
and the measured 184 / 666 / 2846 ms grow by a factor of four per doubling, as a quadratic
cost does.  The `chainflat` and `split` controls are cheap here only because their answer is
a path of one resp. two edges.

So the per-expansion cost of the lazily deleted heap is flat, as the data structure promises;
what is quadratic is the *path reconstruction*, which is shared by every implementation in
this library and is independent of the queue representation.  The two controls and the
`flattrace` mode are in this file so that the effect can be measured again after a change.
-/

open WeightedDiGraph NatGraph

/-! ## The grid graph -/

/-- Neighbours in the `n × n` grid: the right and the downward neighbour. -/
def lazyGridNbrs (n : ℕ) (i : Fin (n * n)) : List (Fin (n * n)) :=
  (if h1 : i.val % n + 1 < n ∧ i.val + 1 < n * n then [(⟨i.val + 1, h1.2⟩ : Fin (n * n))]
    else []) ++
  (if h2 : i.val + n < n * n then [(⟨i.val + n, h2⟩ : Fin (n * n))] else [])

theorem lazyGridNbrs_pairwise_lt (n : ℕ) (i : Fin (n * n)) :
    (lazyGridNbrs n i).Pairwise (· < ·) := by
  unfold lazyGridNbrs
  split_ifs with h1 h2 h2 <;>
    simp only [List.nil_append, List.append_nil, List.singleton_append]
  · refine List.pairwise_cons.mpr ⟨?_, List.pairwise_singleton _ _⟩
    intro b hb
    simp only [List.mem_singleton] at hb
    subst hb
    refine Fin.mk_lt_mk.mpr ?_
    have hn : 1 < n := by omega
    omega
  · exact List.pairwise_singleton _ _
  · exact List.pairwise_singleton _ _
  · exact List.Pairwise.nil

/-- The `n × n` grid graph with data-dependent edge costs. -/
def lazyGridGraph (n : ℕ) : NatGraphWithGenerator (Fin (n * n)) where
  Adj u v := v ∈ lazyGridNbrs n u
  Payload u v _ := (u.val * 7 + v.val * 13) % 9 + 1
  instDecAdj u v := inferInstanceAs (Decidable (v ∈ lazyGridNbrs n u))
  neighbours := lazyGridNbrs n
  neighbours_are_adj _ _ := Iff.rfl
  neighbours_sublist u := by
    rw [toList_univ_finEnum_eq_finRange (n * n)]
    exact sublist_finRange_of_pairwise_lt _ (lazyGridNbrs_pairwise_lt n u)

/-! ## The binary tree (no decrease-keys) -/

/-- Neighbours in the complete binary tree on `Fin n`: the children `2i+1`, `2i+2`. -/
def lazyTreeNbrs (n : ℕ) (i : Fin n) : List (Fin n) :=
  if h1 : 2 * i.val + 1 < n then
    if h2 : 2 * i.val + 2 < n then [⟨2 * i.val + 1, h1⟩, ⟨2 * i.val + 2, h2⟩]
    else [⟨2 * i.val + 1, h1⟩]
  else []

theorem lazyTreeNbrs_pairwise_lt (n : ℕ) (i : Fin n) :
    (lazyTreeNbrs n i).Pairwise (· < ·) := by
  unfold lazyTreeNbrs
  split
  · split
    · refine List.pairwise_cons.mpr ⟨?_, List.pairwise_singleton _ _⟩
      intro b hb
      rw [List.mem_singleton] at hb
      subst hb
      exact Fin.mk_lt_mk.mpr (by omega)
    · exact List.pairwise_singleton _ _
  · exact List.Pairwise.nil

/-- The binary-tree graph. -/
def lazyTreeGraph (n : ℕ) : NatGraphWithGenerator (Fin n) where
  Adj u v := v ∈ lazyTreeNbrs n u
  Payload _ v _ := v.val % 5 + 1
  instDecAdj u v := inferInstanceAs (Decidable (v ∈ lazyTreeNbrs n u))
  neighbours := lazyTreeNbrs n
  neighbours_are_adj _ _ := Iff.rfl
  neighbours_sublist u := by
    rw [toList_univ_finEnum_eq_finRange n]
    exact sublist_finRange_of_pairwise_lt _ (lazyTreeNbrs_pairwise_lt n u)

/-! ## The chain-broom (a decrease-key on a large queue in every expansion) -/

/-- Neighbours of the *chain-broom*: vertex `0` sees every other vertex, and every vertex
`i ≠ 0` sees `i + 1`. -/
def lazyChainNbrs (n : ℕ) (i : Fin n) : List (Fin n) :=
  if i.val = 0 then (List.finRange n).drop 1
  else if h : i.val + 1 < n then [⟨i.val + 1, h⟩] else []

theorem lazyChainNbrs_sublist (n : ℕ) (i : Fin n) :
    (lazyChainNbrs n i).Sublist (List.finRange n) := by
  unfold lazyChainNbrs
  split
  · exact List.drop_sublist 1 _
  · split
    · exact sublist_finRange_of_pairwise_lt _ (List.pairwise_singleton _ _)
    · exact List.nil_sublist _

/-- The chain-broom: the direct edge `0 → v` costs `5 * v`, the chain edge `i → i + 1`
costs `1`.  Expanding `0` fills the queue with `|V| - 1` nodes, and expanding `i` then
improves the path order of `i + 1`, which is still in that queue: **every** expansion is a
decrease-key on a queue of size `|V| - i`.  This is the case the lazily deleted heap is meant
to fix — the eagerly updated heap has to rebuild the queue each time. -/
def lazyChainGraph (n : ℕ) : NatGraphWithGenerator (Fin n) where
  Adj u v := v ∈ lazyChainNbrs n u
  Payload u v _ := if u.val = 0 then 5 * v.val else 1
  instDecAdj u v := inferInstanceAs (Decidable (v ∈ lazyChainNbrs n u))
  neighbours := lazyChainNbrs n
  neighbours_are_adj _ _ := Iff.rfl
  neighbours_sublist u := by
    rw [toList_univ_finEnum_eq_finRange n]
    exact lazyChainNbrs_sublist n u

/-- The control experiment for the chain-broom: the *same* graph structure, but the chain
edge is so expensive that it never improves anything.  The queue is just as large and just as
many nodes are expanded, only no decrease-key ever happens — so the difference to
`lazyChainGraph` is the price of the decrease-keys. -/
def lazyChainFlatGraph (n : ℕ) : NatGraphWithGenerator (Fin n) where
  Adj u v := v ∈ lazyChainNbrs n u
  Payload u v _ := if u.val = 0 then 5 * v.val else 5 * n
  instDecAdj u v := inferInstanceAs (Decidable (v ∈ lazyChainNbrs n u))
  neighbours := lazyChainNbrs n
  neighbours_are_adj _ _ := Iff.rfl
  neighbours_sublist u := by
    rw [toList_univ_finEnum_eq_finRange n]
    exact lazyChainNbrs_sublist n u

/-- Neighbours of the *split-broom*: vertex `0` sees every even vertex, and an even vertex
`i` sees `i + 1`, which nobody else has queued. -/
def lazySplitNbrs (n : ℕ) (i : Fin n) : List (Fin n) :=
  if i.val = 0 then (List.finRange n).filter (fun v => v.val % 2 == 0 && v.val != 0)
  else if h : i.val % 2 = 0 ∧ i.val + 1 < n then [⟨i.val + 1, h.2⟩] else []

theorem lazySplitNbrs_sublist (n : ℕ) (i : Fin n) :
    (lazySplitNbrs n i).Sublist (List.finRange n) := by
  unfold lazySplitNbrs
  split
  · exact List.filter_sublist
  · split
    · exact sublist_finRange_of_pairwise_lt _ (List.pairwise_singleton _ _)
    · exact List.nil_sublist _

/-- The control experiment for a *large queue with an insertion in every expansion*: the
queue is filled with the even vertices, and expanding an even vertex queues the odd vertex
after it — a **new** node, never a decrease-key. -/
def lazySplitGraph (n : ℕ) : NatGraphWithGenerator (Fin n) where
  Adj u v := v ∈ lazySplitNbrs n u
  Payload u v _ := if u.val = 0 then 5 * v.val else 1
  instDecAdj u v := inferInstanceAs (Decidable (v ∈ lazySplitNbrs n u))
  neighbours := lazySplitNbrs n
  neighbours_are_adj _ _ := Iff.rfl
  neighbours_sublist u := by
    rw [toList_univ_finEnum_eq_finRange n]
    exact lazySplitNbrs_sublist n u

/-! ## Timing helpers -/

/-- Whether a search returned a path (a plain constructor `match`). -/
@[inline] def lazyFound {α : Type} : Option α → Bool
  | some _ => true
  | none => false

def lazyReport (label : String) (found : Bool) (t0 t1 : Nat) (steps : Nat) : IO Unit := do
  let us := (t1 - t0) / 1000
  let per := if steps = 0 then 0 else (t1 - t0) / steps
  IO.println s!"  {label}: found={found}, {us / 1000} ms ({us} µs), ~{steps} expansions, \
{per} ns/expansion"
  (← IO.getStdout).flush

/-! ## The individual experiments -/

/-- `n × n` grid, goal = the last vertex, eagerly updated heap. -/
def runGridHeap (n : Nat) : IO Unit := do
  if h : 1 < n * n then
    let t0 ← IO.monoNanosNow
    let r := lazyFound (dijkstra_heap (lazyGridGraph n) ⟨0, by omega⟩ ⟨n * n - 1, by omega⟩)
    let t1 ← IO.monoNanosNow
    lazyReport s!"grid heap      {n}x{n}" r t0 t1 (n * n)
  else IO.println "  (need n > 1)"

/-- `n × n` grid, goal = the last vertex, lazily deleted heap (tracing off). -/
def runGridLazy (n : Nat) : IO Unit := do
  if h : 1 < n * n then
    let t0 ← IO.monoNanosNow
    let r := lazyFound
      (dijkstra_heap_lazy (lazyGridGraph n) ⟨0, by omega⟩ ⟨n * n - 1, by omega⟩ 0)
    let t1 ← IO.monoNanosNow
    lazyReport s!"grid heap_lazy {n}x{n}" r t0 t1 (n * n)
  else IO.println "  (need n > 1)"

/-- `n × n` grid with the progress trace switched on. -/
def runGridTrace (n : Nat) (every : Nat) : IO Unit := do
  if h : 1 < n * n then
    let r := lazyFound
      (dijkstra_heap_lazy (lazyGridGraph n) ⟨0, by omega⟩ ⟨n * n - 1, by omega⟩ every)
    IO.println s!"  grid heap_lazy {n}x{n} (trace every {every}): found={r}"
  else IO.println "  (need n > 1)"

/-- Binary tree with `n` vertices, eagerly updated heap. -/
def runTreeHeap (n : Nat) : IO Unit := do
  if h : 1 < n then
    let t0 ← IO.monoNanosNow
    let r := lazyFound (dijkstra_heap (lazyTreeGraph n) ⟨0, by omega⟩ ⟨n - 1, by omega⟩)
    let t1 ← IO.monoNanosNow
    lazyReport s!"tree heap      |V|={n}" r t0 t1 n
  else IO.println "  (need |V| > 1)"

/-- Binary tree with `n` vertices, lazily deleted heap. -/
def runTreeLazy (n : Nat) : IO Unit := do
  if h : 1 < n then
    let t0 ← IO.monoNanosNow
    let r := lazyFound (dijkstra_heap_lazy (lazyTreeGraph n) ⟨0, by omega⟩ ⟨n - 1, by omega⟩ 0)
    let t1 ← IO.monoNanosNow
    lazyReport s!"tree heap_lazy |V|={n}" r t0 t1 n
  else IO.println "  (need |V| > 1)"


/-! ## A path graph: the queue stays of size one, the maps grow -/

/-- Neighbours in the path `0 → 1 → … → n-1`. -/
def lazyPathNbrs (n : ℕ) (i : Fin n) : List (Fin n) :=
  if h : i.val + 1 < n then [⟨i.val + 1, h⟩] else []

theorem lazyPathNbrs_pairwise_lt (n : ℕ) (i : Fin n) :
    (lazyPathNbrs n i).Pairwise (· < ·) := by
  unfold lazyPathNbrs
  split
  · exact List.pairwise_singleton _ _
  · exact List.Pairwise.nil

/-- The path graph. -/
def lazyPathGraph (n : ℕ) : NatGraphWithGenerator (Fin n) where
  Adj u v := v ∈ lazyPathNbrs n u
  Payload _ v _ := v.val % 5 + 1
  instDecAdj u v := inferInstanceAs (Decidable (v ∈ lazyPathNbrs n u))
  neighbours := lazyPathNbrs n
  neighbours_are_adj _ _ := Iff.rfl
  neighbours_sublist u := by
    rw [toList_univ_finEnum_eq_finRange n]
    exact sublist_finRange_of_pairwise_lt _ (lazyPathNbrs_pairwise_lt n u)

/-- Path with `n` vertices, eagerly updated heap. -/
def runPathHeap (n : Nat) : IO Unit := do
  if h : 1 < n then
    let t0 ← IO.monoNanosNow
    let r := lazyFound (dijkstra_heap (lazyPathGraph n) ⟨0, by omega⟩ ⟨n - 1, by omega⟩)
    let t1 ← IO.monoNanosNow
    lazyReport s!"path heap      |V|={n}" r t0 t1 n
  else IO.println "  (need |V| > 1)"

/-- Path with `n` vertices, lazily deleted heap. -/
def runPathLazy (n : Nat) : IO Unit := do
  if h : 1 < n then
    let t0 ← IO.monoNanosNow
    let r := lazyFound (dijkstra_heap_lazy (lazyPathGraph n) ⟨0, by omega⟩ ⟨n - 1, by omega⟩ 0)
    let t1 ← IO.monoNanosNow
    lazyReport s!"path heap_lazy |V|={n}" r t0 t1 n
  else IO.println "  (need |V| > 1)"

/-- Path with `n` vertices, sorted-list queue. -/
def runPathSorted (n : Nat) : IO Unit := do
  if h : 1 < n then
    let t0 ← IO.monoNanosNow
    let r := lazyFound (dijkstra_sorted (lazyPathGraph n) ⟨0, by omega⟩ ⟨n - 1, by omega⟩)
    let t1 ← IO.monoNanosNow
    lazyReport s!"path sorted    |V|={n}" r t0 t1 n
  else IO.println "  (need |V| > 1)"

/-- Path with `n` vertices, unsorted fast state. -/
def runPathFast (n : Nat) : IO Unit := do
  if h : 1 < n then
    let t0 ← IO.monoNanosNow
    let r := lazyFound (dijkstra_fast (lazyPathGraph n) ⟨0, by omega⟩ ⟨n - 1, by omega⟩)
    let t1 ← IO.monoNanosNow
    lazyReport s!"path fast      |V|={n}" r t0 t1 n
  else IO.println "  (need |V| > 1)"

/-! ## A path graph whose last vertex is unreachable: no path is extracted at the end -/

/-- Neighbours in the path `0 → 1 → … → n-2`; the vertex `n-1` has no incoming edge. -/
def lazyCutNbrs (n : ℕ) (i : Fin n) : List (Fin n) :=
  if h : i.val + 1 < n - 1 then [⟨i.val + 1, by omega⟩] else []

theorem lazyCutNbrs_pairwise_lt (n : ℕ) (i : Fin n) :
    (lazyCutNbrs n i).Pairwise (· < ·) := by
  unfold lazyCutNbrs
  split
  · exact List.pairwise_singleton _ _
  · exact List.Pairwise.nil

/-- The path graph with an unreachable last vertex. -/
def lazyCutGraph (n : ℕ) : NatGraphWithGenerator (Fin n) where
  Adj u v := v ∈ lazyCutNbrs n u
  Payload _ v _ := v.val % 5 + 1
  instDecAdj u v := inferInstanceAs (Decidable (v ∈ lazyCutNbrs n u))
  neighbours := lazyCutNbrs n
  neighbours_are_adj _ _ := Iff.rfl
  neighbours_sublist u := by
    rw [toList_univ_finEnum_eq_finRange n]
    exact sublist_finRange_of_pairwise_lt _ (lazyCutNbrs_pairwise_lt n u)

/-- Unreachable-goal path, eagerly updated heap. -/
def runCutHeap (n : Nat) : IO Unit := do
  if h : 1 < n then
    let t0 ← IO.monoNanosNow
    let r := lazyFound (dijkstra_heap (lazyCutGraph n) ⟨0, by omega⟩ ⟨n - 1, by omega⟩)
    let t1 ← IO.monoNanosNow
    lazyReport s!"cut  heap      |V|={n}" r t0 t1 n
  else IO.println "  (need |V| > 1)"

/-- Unreachable-goal path, lazily deleted heap. -/
def runCutLazy (n : Nat) : IO Unit := do
  if h : 1 < n then
    let t0 ← IO.monoNanosNow
    let r := lazyFound (dijkstra_heap_lazy (lazyCutGraph n) ⟨0, by omega⟩ ⟨n - 1, by omega⟩ 0)
    let t1 ← IO.monoNanosNow
    lazyReport s!"cut  heap_lazy |V|={n}" r t0 t1 n
  else IO.println "  (need |V| > 1)"

/-- Chain-broom with `n` vertices, eagerly updated heap. -/
def runChainHeap (n : Nat) : IO Unit := do
  if h : 1 < n then
    let t0 ← IO.monoNanosNow
    let r := lazyFound (dijkstra_heap (lazyChainGraph n) ⟨0, by omega⟩ ⟨n - 1, by omega⟩)
    let t1 ← IO.monoNanosNow
    lazyReport s!"chain heap      |V|={n}" r t0 t1 n
  else IO.println "  (need |V| > 1)"

/-- Chain-broom with `n` vertices, lazily deleted heap. -/
def runChainLazy (n : Nat) : IO Unit := do
  if h : 1 < n then
    let t0 ← IO.monoNanosNow
    let r := lazyFound (dijkstra_heap_lazy (lazyChainGraph n) ⟨0, by omega⟩ ⟨n - 1, by omega⟩ 0)
    let t1 ← IO.monoNanosNow
    lazyReport s!"chain heap_lazy |V|={n}" r t0 t1 n
  else IO.println "  (need |V| > 1)"

/-- Chain-broom with the progress trace switched on; pipe stderr through a tool such as
`awk '{ print systime(), $0 }'` to see how the cost per expansion develops. -/
def runChainTrace (n : Nat) (every : Nat) : IO Unit := do
  if h : 1 < n then
    let r := lazyFound
      (dijkstra_heap_lazy (lazyChainGraph n) ⟨0, by omega⟩ ⟨n - 1, by omega⟩ every)
    IO.println s!"  chain heap_lazy |V|={n} (trace every {every}): found={r}"
  else IO.println "  (need |V| > 1)"

/-- The `chainflat` control with the progress trace switched on, so that the cost of the
first expansions can be compared with `runChainTrace`. -/
def runChainFlatTrace (n : Nat) (every : Nat) : IO Unit := do
  if h : 1 < n then
    let r := lazyFound
      (dijkstra_heap_lazy (lazyChainFlatGraph n) ⟨0, by omega⟩ ⟨n - 1, by omega⟩ every)
    IO.println s!"  flat  heap_lazy |V|={n} (trace every {every}): found={r}"
  else IO.println "  (need |V| > 1)"

/-- The control experiment: chain-broom without decrease-keys, lazily deleted heap. -/
def runChainFlatLazy (n : Nat) : IO Unit := do
  if h : 1 < n then
    let t0 ← IO.monoNanosNow
    let r := lazyFound
      (dijkstra_heap_lazy (lazyChainFlatGraph n) ⟨0, by omega⟩ ⟨n - 1, by omega⟩ 0)
    let t1 ← IO.monoNanosNow
    lazyReport s!"flat  heap_lazy |V|={n}" r t0 t1 n
  else IO.println "  (need |V| > 1)"

/-- The control experiment: split-broom (a *new* node queued in every expansion), lazily
deleted heap. -/
def runSplitLazy (n : Nat) : IO Unit := do
  if h : 1 < n then
    let t0 ← IO.monoNanosNow
    let r := lazyFound
      (dijkstra_heap_lazy (lazySplitGraph n) ⟨0, by omega⟩ ⟨n - 1, by omega⟩ 0)
    let t1 ← IO.monoNanosNow
    lazyReport s!"split heap_lazy |V|={n}" r t0 t1 n
  else IO.println "  (need |V| > 1)"

/-- Chain-broom with `n` vertices, sorted-list queue. -/
def runChainSorted (n : Nat) : IO Unit := do
  if h : 1 < n then
    let t0 ← IO.monoNanosNow
    let r := lazyFound (dijkstra_sorted (lazyChainGraph n) ⟨0, by omega⟩ ⟨n - 1, by omega⟩)
    let t1 ← IO.monoNanosNow
    lazyReport s!"chain sorted    |V|={n}" r t0 t1 n
  else IO.println "  (need |V| > 1)"

def lazySuite : IO Unit := do
  IO.println "== grid: every vertex is relaxed twice, so decrease-keys happen throughout =="
  runGridHeap 60
  runGridLazy 60
  runGridHeap 100
  runGridLazy 100
  runGridHeap 150
  runGridLazy 150
  IO.println "== binary tree: no decrease-key ever happens =="
  runTreeHeap 20000
  runTreeLazy 20000
  runTreeHeap 40000
  runTreeLazy 40000
  IO.println "== chain-broom: a decrease-key on a queue of size |V|-i in every expansion =="
  runChainSorted 2000
  runChainHeap 2000
  runChainLazy 2000
  runChainHeap 4000
  runChainLazy 4000
  runChainLazy 8000
  runChainLazy 16000

def main (args : List String) : IO Unit := do
  match args with
  | ["grid", n] => do runGridHeap n.toNat!; runGridLazy n.toNat!
  | ["gridlazy", n] => runGridLazy n.toNat!
  | ["gridheap", n] => runGridHeap n.toNat!
  | ["tree", n] => do runTreeHeap n.toNat!; runTreeLazy n.toNat!
  | ["chain", n] => do runChainHeap n.toNat!; runChainLazy n.toNat!
  | ["chainlazy", n] => runChainLazy n.toNat!
  | ["chainsorted", n] => runChainSorted n.toNat!
  | ["chaintrace", n] => runChainTrace n.toNat! 1000
  | ["chaintrace", n, e] => runChainTrace n.toNat! e.toNat!
  | ["chainflat", n] => runChainFlatLazy n.toNat!
  | ["flattrace", n, e] => runChainFlatTrace n.toNat! e.toNat!
  | ["split", n] => runSplitLazy n.toNat!
  | ["trace", n] => runGridTrace n.toNat! 1000
  | ["cut", n] => do runCutHeap n.toNat!; runCutLazy n.toNat!
  | ["path", n] => do runPathSorted n.toNat!; runPathFast n.toNat!; runPathHeap n.toNat!; runPathLazy n.toNat!
  | _ => lazySuite
