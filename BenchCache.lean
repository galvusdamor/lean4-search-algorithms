import SearchAlgorithms.AStarCached
import BenchAux

/-!
# Benchmark: caching the heuristic

The heuristic is a pure function of the vertex, so `heur v` has to be computed **once**.  An
uncached search computes it far more often than that:

* once per neighbour of every expanded node (the test `heur v ≠ ⊤`), and
* twice per comparison in the queue — and a heap operation performs `O(log m)` comparisons,
  so one expansion of a node of degree `d` costs `Θ(d · log m)` heuristic evaluations.

`SearchAlgorithms.HeuristicCache` provides a cache that is pure, is *provably* the function
it caches, and evaluates it at most once per vertex.  This benchmark measures what that is
worth.

## The experiment

`gridGraphCache n` is the `n × n` grid with data-dependent edge costs (all at least `1`), and
the searches run from the top-left to the bottom-right corner.  The heuristic is the
Manhattan distance to the goal — which is admissible — plus a **deliberately expensive**
computation of `work` iterations whose value is `0`.  `work` is the knob: it stands for the
pattern database, the relaxed sub-search or the landmark distances of a real application.

Three implementations are compared, all of which are *proved* to return the same path
(`astar_heap_lazy_trie_eq`, `astar_heap_lazy_array_eq`):

* `astar_heap_lazy_fastpath` — no cache;
* `astar_heap_lazy_trie` — the lazily built binary trie cache: `O(1)` to create, one step
  per *bit* of the vertex number per lookup, memory only for the vertices actually looked at;
* `astar_heap_lazy_wtrie` — the same with sixteen children per node: one step per *four*
  bits;
* `astar_heap_lazy_chunked` — chunks of 1024 thunks, each allocated when first touched: two
  array indexings per lookup;
* `astar_heap_lazy_array` — a flat array of `|V|` unevaluated thunks: `O(1)` per lookup.

Usage:

```
lake exe benchcache                  -- the standard suite
lake exe benchcache grid 100 200     -- one 100×100 grid, 200 iterations of work per call
lake exe benchcache count 4 0        -- 4×4 grid, printing one line per heuristic evaluation
```

The `count` mode prints one line on stderr for every evaluation of the heuristic, so

```
lake exe benchcache count 8 0 2>&1 >/dev/null | grep -c HEUR
```

counts them per implementation: with a cache the number is the number of *distinct vertices*
the search looks at (35 of the 36 vertices of the 6×6 grid), without a cache it is several
times larger (361).
-/

open WeightedDiGraph NatGraph SearchAlgorithms

/-! ## The grid -/

/-- Neighbours in the `n × n` grid: the right and the downward neighbour. -/
def cacheGridNbrs (n : ℕ) (i : Fin (n * n)) : List (Fin (n * n)) :=
  (if h1 : i.val % n + 1 < n ∧ i.val + 1 < n * n then [(⟨i.val + 1, h1.2⟩ : Fin (n * n))]
    else []) ++
  (if h2 : i.val + n < n * n then [(⟨i.val + n, h2⟩ : Fin (n * n))] else [])

theorem cacheGridNbrs_pairwise_lt (n : ℕ) (i : Fin (n * n)) :
    (cacheGridNbrs n i).Pairwise (· < ·) := by
  unfold cacheGridNbrs
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

/-- The `n × n` grid graph with data-dependent edge costs, all at least `1`. -/
def cacheGridGraph (n : ℕ) : NatGraphWithGenerator (Fin (n * n)) where
  Adj u v := v ∈ cacheGridNbrs n u
  Payload u v _ := (u.val * 7 + v.val * 13) % 9 + 1
  instDecAdj u v := inferInstanceAs (Decidable (v ∈ cacheGridNbrs n u))
  neighbours := cacheGridNbrs n
  neighbours_are_adj _ _ := Iff.rfl
  neighbours_sublist u := by
    rw [toList_univ_finEnum_eq_finRange (n * n)]
    exact sublist_finRange_of_pairwise_lt _ (cacheGridNbrs_pairwise_lt n u)

/-! ## An expensive heuristic -/

/-- `work` iterations of arithmetic whose result is `0`: the stand-in for an expensive
heuristic (a pattern database, a relaxed sub-search, distances to landmarks). -/
def busy (work : ℕ) (v : ℕ) : ℕ :=
  ((List.range work).foldl (fun a i => (a + i * (v + 1)) % 7) 0) % 1

/-- The Manhattan distance from `v` to the bottom-right corner of the `n × n` grid, plus
`work` iterations of useless arithmetic.  Admissible: every edge costs at least `1`. -/
def cacheHeur (n : ℕ) (work : ℕ) (v : Fin (n * n)) : ℕ∞ :=
  ((n - 1 - v.val / n) + (n - 1 - v.val % n) + busy work v.val : ℕ)

/-- The same heuristic, printing one line on stderr per evaluation. -/
def cacheHeurTraced (n : ℕ) (work : ℕ) (v : Fin (n * n)) : ℕ∞ :=
  dbg_trace s!"HEUR {v.val}"; cacheHeur n work v

/-! ## Timing helpers -/

/-- Whether a search returned a path. -/
@[inline] def cacheFound {α : Type} : Option α → Bool
  | some _ => true
  | none => false

def cacheReport (label : String) (found : Bool) (t0 t1 : Nat) (steps : Nat) : IO Unit := do
  let us := (t1 - t0) / 1000
  let per := if steps = 0 then 0 else (t1 - t0) / steps
  IO.println s!"  {label}: found={found}, {us / 1000} ms ({us} µs), ~{steps} expansions, \
{per} ns/expansion"
  (← IO.getStdout).flush

/-! ## The experiments -/

/-- A\* on the `n × n` grid **without** a cache. -/
def runGridPlain (n : Nat) (work : Nat) : IO Unit := do
  if h : 1 < n * n then
    let t0 ← IO.monoNanosNow
    let r := cacheFound (astar_heap_lazy_fastpath (cacheGridGraph n) (cacheHeur n work)
      ⟨0, by omega⟩ ⟨n * n - 1, by omega⟩ 0)
    let t1 ← IO.monoNanosNow
    cacheReport s!"grid {n}x{n} work={work} uncached" r t0 t1 (n * n)
  else IO.println "  (need n > 1)"

/-- A\* on the `n × n` grid with the **lazily built trie** cache. -/
def runGridTrie (n : Nat) (work : Nat) : IO Unit := do
  if h : 1 < n * n then
    let t0 ← IO.monoNanosNow
    let r := cacheFound (astar_heap_lazy_trie (cacheGridGraph n) (VIndex.ofFin (n * n))
      (cacheHeur n work) ⟨0, by omega⟩ ⟨n * n - 1, by omega⟩ 64 0)
    let t1 ← IO.monoNanosNow
    cacheReport s!"grid {n}x{n} work={work} trie     " r t0 t1 (n * n)
  else IO.println "  (need n > 1)"

/-- A\* on the `n × n` grid with the **16-way trie** cache. -/
def runGridWTrie (n : Nat) (work : Nat) : IO Unit := do
  if h : 1 < n * n then
    let t0 ← IO.monoNanosNow
    let r := cacheFound (astar_heap_lazy_wtrie (cacheGridGraph n) (VIndex.ofFin (n * n))
      (cacheHeur n work) ⟨0, by omega⟩ ⟨n * n - 1, by omega⟩ 16 0)
    let t1 ← IO.monoNanosNow
    cacheReport s!"grid {n}x{n} work={work} wtrie    " r t0 t1 (n * n)
  else IO.println "  (need n > 1)"

/-- A\* on the `n × n` grid with the **chunked** cache (chunks of 1024). -/
def runGridChunked (n : Nat) (work : Nat) : IO Unit := do
  if h : 1 < n * n then
    let t0 ← IO.monoNanosNow
    let r := cacheFound (astar_heap_lazy_chunked (cacheGridGraph n) (VIndex.ofFin (n * n))
      (cacheHeur n work) 1024 (n * n / 1024 + 1) ⟨0, by omega⟩ ⟨n * n - 1, by omega⟩ 0)
    let t1 ← IO.monoNanosNow
    cacheReport s!"grid {n}x{n} work={work} chunked  " r t0 t1 (n * n)
  else IO.println "  (need n > 1)"

/-- A\* on the `n × n` grid with the **flat array** cache. -/
def runGridArray (n : Nat) (work : Nat) : IO Unit := do
  if h : 1 < n * n then
    let t0 ← IO.monoNanosNow
    let r := cacheFound (astar_heap_lazy_array (cacheGridGraph n) (VIndex.ofFin (n * n))
      (cacheHeur n work) (n * n) ⟨0, by omega⟩ ⟨n * n - 1, by omega⟩ 0)
    let t1 ← IO.monoNanosNow
    cacheReport s!"grid {n}x{n} work={work} array    " r t0 t1 (n * n)
  else IO.println "  (need n > 1)"

/-- Print one line per heuristic evaluation, without and with the cache. -/
def runCount (n : Nat) (work : Nat) : IO Unit := do
  if h : 1 < n * n then
    IO.println s!"  --- uncached, {n}x{n} ---"
    (← IO.getStdout).flush
    let r := cacheFound (astar_heap_lazy_fastpath (cacheGridGraph n) (cacheHeurTraced n work)
      ⟨0, by omega⟩ ⟨n * n - 1, by omega⟩ 0)
    IO.println s!"  found={r}"
    IO.println s!"  --- trie cache, {n}x{n} ---"
    (← IO.getStdout).flush
    let r2 := cacheFound (astar_heap_lazy_trie (cacheGridGraph n) (VIndex.ofFin (n * n))
      (cacheHeurTraced n work) ⟨0, by omega⟩ ⟨n * n - 1, by omega⟩ 64 0)
    IO.println s!"  found={r2}"
    IO.println s!"  --- wtrie cache, {n}x{n} ---"
    (← IO.getStdout).flush
    let r3 := cacheFound (astar_heap_lazy_wtrie (cacheGridGraph n) (VIndex.ofFin (n * n))
      (cacheHeurTraced n work) ⟨0, by omega⟩ ⟨n * n - 1, by omega⟩ 16 0)
    IO.println s!"  found={r3}"
    IO.println s!"  --- chunked cache, {n}x{n} ---"
    (← IO.getStdout).flush
    let r4 := cacheFound (astar_heap_lazy_chunked (cacheGridGraph n) (VIndex.ofFin (n * n))
      (cacheHeurTraced n work) 8 (n * n / 8 + 1) ⟨0, by omega⟩ ⟨n * n - 1, by omega⟩ 0)
    IO.println s!"  found={r4}"
    IO.println s!"  --- array cache, {n}x{n} ---"
    (← IO.getStdout).flush
    let r5 := cacheFound (astar_heap_lazy_array (cacheGridGraph n) (VIndex.ofFin (n * n))
      (cacheHeurTraced n work) (n * n) ⟨0, by omega⟩ ⟨n * n - 1, by omega⟩ 0)
    IO.println s!"  found={r5}"
  else IO.println "  (need n > 1)"

def runSuite : IO Unit := do
  IO.println "cheap heuristic (work = 0): the cache costs a little and saves a little"
  for n in [50, 100] do
    runGridPlain n 0
    runGridTrie n 0
    runGridWTrie n 0
    runGridChunked n 0
    runGridArray n 0
  IO.println "moderately expensive heuristic (work = 50)"
  for n in [50, 100] do
    runGridPlain n 50
    runGridTrie n 50
    runGridWTrie n 50
    runGridChunked n 50
    runGridArray n 50
  IO.println "expensive heuristic (work = 500)"
  for n in [50, 100] do
    runGridPlain n 500
    runGridTrie n 500
    runGridWTrie n 500
    runGridChunked n 500
    runGridArray n 500

def main (args : List String) : IO Unit := do
  match args with
  | ["grid", n, w] => match n.toNat?, w.toNat? with
    | some n, some w => do runGridPlain n w; runGridTrie n w; runGridWTrie n w; runGridChunked n w; runGridArray n w
    | _, _ => IO.println "usage: benchcache grid <n> <work>"
  | ["count", n, w] => match n.toNat?, w.toNat? with
    | some n, some w => runCount n w
    | _, _ => IO.println "usage: benchcache count <n> <work>"
  | [] => runSuite
  | _ => IO.println "usage: benchcache [grid <n> <work> | count <n> <work>]"
