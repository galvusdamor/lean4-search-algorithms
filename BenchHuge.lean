import SearchAlgorithms.DijkstraFast
import SearchAlgorithms.DijkstraSorted
import BenchAux

/-!
# Benchmark: *large* graphs with a *large* queue

`BenchBroom` measures a graph whose queue reaches size `|V| - 1`, but only up to a few
thousand vertices.  This file scales the same idea up to `|V| = 10⁷` and adds a second family
in which the queue keeps growing *throughout* the search, so that the two costs can be told
apart:

* **`broom n`** — vertex `0` is connected to all other vertices (edge cost `v + 1`), every
  other vertex is a sink.  The first expansion puts `n - 1` nodes into the queue, and every
  later expansion pops one and queues nothing.  The queue is *filled once* and then drained.
* **`tree n`** — vertex `i` has out-edges to `2i+1` and `2i+2` (a complete binary tree) with
  edge costs `(v % 5) + 1`.  Every expansion queues two new nodes at a data-dependent position
  of the queue, so the queue grows to `Θ(n)` *and* is written to in every step.

Both are run with `dijkstra_sorted` (the implementation with the maintained sorted queue); the
broom is also run with `dijkstra_fast` at small sizes for reference.

## Measured (`lake exe benchhuge`, 8-core x86-64 Linux container)

### Broom: a queue of up to 10⁷ nodes

| `|V|` | goal = `|V|-1` (queue drained) | goal popped 1st | RSS |
|------:|-------------------------------:|----------------:|----:|
| 10⁴   | 13 ms                          | —               | 93 MiB |
| 10⁵   | 207 ms                         | —               | 119 MiB |
| 10⁶   | 2.25 s                         | 2.03 s          | 380 MiB |
| 10⁷   | 22.4 s                         | 22.0 s          | 3.1 GiB |

(The `RSS` column is only meaningful for a single run per process, i.e. for
`lake exe benchhuge broom …`; in the full suite the runs share one process.  An empty run of
the executable already has ≈ 88 MiB resident.  Times vary by ≈ ± 20 % between runs;
`bench-results-huge.txt` records one complete run of the suite.)

So a search over a graph with **10 million** vertices and a queue holding **all** of them
completes in ≈ 22 s, and the time is **linear** in `|V|` (2.2 µs per queued node at every
size).  The comparison with the third column localises where that time goes: a run that stops
after the *first* pop costs the same, i.e. essentially the whole 22 s is the single expansion
that *creates* the 10⁷ queue entries (hash-map inserts for path order and mother, and one
`mergeSort` of a 10⁷-element list), while the 10⁷ subsequent pops together cost only the
difference of the two columns (0.4 s … 1.5 s depending on the run), i.e. **well under 150 ns
per pop from a 10-million-element queue**.  For reference, `dijkstra_fast`, which
re-sorts the queue on every expansion, needs 0.25 s already for `|V| = 1000` and 1.09 s for
`|V| = 2000` (a factor of 4 per doubling), and is hopeless at these sizes.

### Binary tree: a queue that keeps growing

| `|V|` | `dijkstra_sorted` | per expansion |
|------:|------------------:|--------------:|
| 5000  | 0.22 s            | 45 µs |
| 10000 | 0.92 s            | 92 µs |
| 20000 | 3.85 s            | 192 µs |
| 40000 | 16.0 s            | 401 µs |

Here the time *quadruples* when `|V|` doubles: the cost per expansion is proportional to the
current queue length (≈ 20 ns per queue element).  This is the price of representing the queue
as a sorted **list**: inserting a node costs `O(position)`, and the children of the popped
node land far inside the queue — with only five distinct edge costs, many queued nodes share
the `f`-value of a new node, and the merge places it after all of them.  The broom does not
show this because there the queue is filled once and afterwards only popped, which is `O(1)`
per step.
Making searches whose queue keeps growing scale as well as the broom would need a different
queue *data structure* (a heap or a search tree) rather than a sorted list — that is a change
to the state representation, provable by the same `hsearch_step_expand_…_eq` scheme that the
fast and sorted states use, but it is not part of the present implementations.

Usage:

```
lake exe benchhuge                 -- the standard suite
lake exe benchhuge broom  10000000 -- one broom run, goal = the most expensive vertex
lake exe benchhuge broomhit 10000000 5   -- broom, goal = vertex 5 (found after 1 pop)
lake exe benchhuge tree   1000000  -- one tree run
lake exe benchhuge fast   2000     -- broom with the (quadratic) `dijkstra_fast`
```

The sizes are run-time arguments on purpose: a *closed* search expression is lifted by the
compiler and evaluated at module initialisation, i.e. outside the timed region (see the
methodology notes in `Bench`).
-/

open WeightedDiGraph NatGraph

/-! ## The broom graph (queue filled once, then drained) -/

/-- Neighbours of the broom graph: vertex `0` sees everybody else, all other vertices are
sinks. -/
def hugeBroomNbrs (n : ℕ) (i : Fin n) : List (Fin n) :=
  if i.val = 0 then (List.finRange n).drop 1 else []

theorem hugeBroomNbrs_sublist (n : ℕ) (i : Fin n) :
    (hugeBroomNbrs n i).Sublist (List.finRange n) := by
  unfold hugeBroomNbrs
  split
  · exact List.drop_sublist 1 _
  · exact List.nil_sublist _

/-- The broom graph: `0 → v` for every `v ≠ 0`, with edge cost `v + 1`. -/
def hugeBroomGraph (n : ℕ) : NatGraphWithGenerator (Fin n) where
  Adj u v := v ∈ hugeBroomNbrs n u
  Payload _ v _ := v.val + 1
  instDecAdj u v := inferInstanceAs (Decidable (v ∈ hugeBroomNbrs n u))
  neighbours := hugeBroomNbrs n
  neighbours_are_adj _ _ := Iff.rfl
  neighbours_sublist u := by
    rw [toList_univ_finEnum_eq_finRange n]; exact hugeBroomNbrs_sublist n u

/-! ## The binary-tree graph (queue grows throughout the search) -/

/-- Neighbours in the complete binary tree on `Fin n`: the children `2i+1`, `2i+2`. -/
def hugeTreeNbrs (n : ℕ) (i : Fin n) : List (Fin n) :=
  if h1 : 2 * i.val + 1 < n then
    if h2 : 2 * i.val + 2 < n then [⟨2 * i.val + 1, h1⟩, ⟨2 * i.val + 2, h2⟩]
    else [⟨2 * i.val + 1, h1⟩]
  else []

theorem hugeTreeNbrs_pairwise_lt (n : ℕ) (i : Fin n) :
    (hugeTreeNbrs n i).Pairwise (· < ·) := by
  unfold hugeTreeNbrs
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
def hugeTreeGraph (n : ℕ) : NatGraphWithGenerator (Fin n) where
  Adj u v := v ∈ hugeTreeNbrs n u
  Payload _ v _ := v.val % 5 + 1
  instDecAdj u v := inferInstanceAs (Decidable (v ∈ hugeTreeNbrs n u))
  neighbours := hugeTreeNbrs n
  neighbours_are_adj _ _ := Iff.rfl
  neighbours_sublist u := by
    rw [toList_univ_finEnum_eq_finRange n]
    exact sublist_finRange_of_pairwise_lt _ (hugeTreeNbrs_pairwise_lt n u)

/-! ## Timing helpers -/

/-- Whether a search returned a path (a plain constructor `match`). -/
@[inline] def hugeFound {α : Type} : Option α → Bool
  | some _ => true
  | none => false

/-- Resident set size of this process, in MiB (Linux `/proc/self/status`): the peak
(`VmHWM`) if the kernel reports it, otherwise the current one (`VmRSS`). -/
def peakRssMiB : IO (Option Nat) := do
  try
    let s ← IO.FS.readFile "/proc/self/status"
    let ls := s.splitOn "\n"
    let some line := (ls.find? (·.startsWith "VmHWM:")).orElse
      (fun _ => ls.find? (·.startsWith "VmRSS:")) | return none
    let some kb := ((line.replace "\t" " ").splitOn " ").filterMap (·.toNat?) |>.head?
      | return none
    return some (kb / 1024)
  catch _ => return none

def report (label : String) (found : Bool) (t0 t1 : Nat) (steps : Nat) : IO Unit := do
  let us := (t1 - t0) / 1000
  let per := if steps = 0 then 0 else (t1 - t0) / steps
  let mem ← peakRssMiB
  IO.println s!"  {label}: found={found}, {us / 1000} ms ({us} µs), ~{steps} expansions, \
{per} ns/expansion, RSS {mem.getD 0} MiB"
  (← IO.getStdout).flush

/-! ## The individual experiments -/

/-- Broom graph with `n` vertices, goal = the *most expensive* vertex `n-1`: the whole queue
of `n-1` nodes has to be drained, i.e. the search performs `n` expansions. -/
def runBroomSorted (n : Nat) : IO Unit := do
  if h : 1 < n then
    let t0 ← IO.monoNanosNow
    let r := hugeFound (dijkstra_sorted (hugeBroomGraph n) ⟨0, by omega⟩ ⟨n - 1, by omega⟩)
    let t1 ← IO.monoNanosNow
    report s!"broom sorted  |V|={n} (drain)" r t0 t1 n
  else IO.println "  (need |V| > 1)"

/-- Broom graph with `n` vertices, goal = vertex `g`: the queue is filled with `n-1` nodes and
then only `g` of them are popped. -/
def runBroomSortedHit (n : Nat) (g : Nat) : IO Unit := do
  if h : 1 < n then
    let t0 ← IO.monoNanosNow
    let r := hugeFound
      (dijkstra_sorted (hugeBroomGraph n) ⟨0, by omega⟩ ⟨g % n, Nat.mod_lt _ (by omega)⟩)
    let t1 ← IO.monoNanosNow
    report s!"broom sorted  |V|={n} (goal {g % n})" r t0 t1 (g % n + 1)
  else IO.println "  (need |V| > 1)"

/-- Broom graph with the hash-set state (queue re-sorted from scratch every expansion). -/
def runBroomFast (n : Nat) : IO Unit := do
  if h : 1 < n then
    let t0 ← IO.monoNanosNow
    let r := hugeFound (dijkstra_fast (hugeBroomGraph n) ⟨0, by omega⟩ ⟨n - 1, by omega⟩)
    let t1 ← IO.monoNanosNow
    report s!"broom fast    |V|={n} (drain)" r t0 t1 n
  else IO.println "  (need |V| > 1)"

/-- Binary tree with `n` vertices, goal = the last vertex `n-1`. -/
def runTreeSorted (n : Nat) : IO Unit := do
  if h : 1 < n then
    let t0 ← IO.monoNanosNow
    let r := hugeFound (dijkstra_sorted (hugeTreeGraph n) ⟨0, by omega⟩ ⟨n - 1, by omega⟩)
    let t1 ← IO.monoNanosNow
    report s!"tree  sorted  |V|={n}" r t0 t1 n
  else IO.println "  (need |V| > 1)"

def suite : IO Unit := do
  IO.println "== broom, dijkstra_sorted: queue of |V|-1 nodes, drained completely =="
  runBroomSorted 100000
  runBroomSorted 1000000
  runBroomSorted 10000000
  IO.println "== broom, dijkstra_sorted: same queue, but the goal is popped early =="
  runBroomSortedHit 1000000 1
  runBroomSortedHit 10000000 1
  IO.println "== broom, dijkstra_fast (queue re-sorted every expansion), for reference =="
  runBroomFast 1000
  runBroomFast 2000
  IO.println "== binary tree: the queue grows throughout the search =="
  runTreeSorted 10000
  runTreeSorted 20000
  runTreeSorted 40000

def main (args : List String) : IO Unit := do
  match args with
  | ["broom", n] => runBroomSorted (n.toNat!)
  | ["broomhit", n, g] => runBroomSortedHit (n.toNat!) (g.toNat!)
  | ["fast", n] => runBroomFast (n.toNat!)
  | ["tree", n] => runTreeSorted (n.toNat!)
  | _ => suite
