import SearchAlgorithms.AStarHeapLazyPath
import SearchAlgorithms.HeuristicCache

/-!
# A\* with a cached heuristic

The heuristic is a pure function of the vertex, so `heur v` only ever needs to be computed
once.  A search does not call it once, though: every neighbour of every expanded node is
tested for `heur v ≠ ⊤`, and the queue comparator computes the `f`-value of both of its
arguments, so a heap operation costs `O(log m)` calls.  When the heuristic is expensive —
a pattern database, a relaxed sub-search, distances to landmarks — that is where the time
goes.

This module runs the searches of `SearchAlgorithms.AStarHeapLazyPath` (the lazily deleted
heap with linear-time path reconstruction, the fastest implementation in the library) with a
**cached** heuristic: a `SearchAlgorithms.CachedHeuristic`, which evaluates `heur v` at most
once per vertex, the first time it is needed, and never at all for a vertex the search does
not touch.

```lean
-- the vertices are `Fin n`, so `Fin.val` numbers them; chunks of 1024
#eval astar_heap_lazy_chunked G (VIndex.ofFin n) heur 1024 (n / 1024 + 1) start goal

-- or keep the cache and use it for several searches:
let hc := CachedFun.ofChunked 1024 (n / 1024 + 1) (VIndex.ofFin n) heur
astar_heap_lazy_fastpath_cached G hc start goal
```

## Correctness is not re-proved

A `CachedHeuristic V heur` carries the proof that the cached function **is** `heur`
(`CachedFun.fn_eq`).  The cached search is therefore literally the uncached search applied to
`heur`, and every statement transfers by rewriting with that equation: `..._cached_eq` gives
equality with `astar`, and soundness, completeness and optimality follow exactly as before.

## Which cache to use

* `CachedFun.ofChunked chunk nchunks vi heur` — chunks of thunks, each allocated when first
  touched: two array indexings per lookup and memory only for the chunks the search visits.
  The best default for dense vertex numbers.
* `CachedFun.ofWTrie vi depth heur` / `CachedFun.ofTrie vi depth heur` — lazily built 16-way
  resp. binary trie: `O(1)` to create, one step per four bits resp. per bit of the vertex
  number, memory proportional to the number of vertices actually looked at.  Use these when
  the vertex numbers are sparse or unbounded.
* `CachedFun.ofArray n vi heur` — a flat array of `n` thunks: `O(1)` per lookup, one cell per
  vertex allocated up front.  Best when the search touches most of a moderate-sized graph.

Both are pure and both evaluate `heur v` at most once per `v`.
-/

namespace NatGraph

open WeightedDiGraph
open SearchAlgorithms

variable {V : Type} [FinEnum V] [BEq V] [LawfulBEq V] [Hashable V]
variable (G : NatGraphWithGenerator V) {heur : V → ℕ∞} (hc : CachedHeuristic V heur)

/-! ## A\* with a cached heuristic -/

/-- **A\* with a lazily deleted heap, linear-time path reconstruction and a cached
heuristic.**  `hc.fn` is `heur`, so this is `astar_heap_lazy_fastpath`; the only difference is
that the heuristic of a vertex is computed once instead of once per comparison. -/
def astar_heap_lazy_fastpath_cached (start : V) (goal : V) (te : ℕ := 100) :
    Option ((G.toWeightedDiGraph).Path start goal) :=
  astar_heap_lazy_fastpath G hc.fn start goal te

/-- The cached search is the uncached one. -/
theorem astar_heap_lazy_fastpath_cached_eq_uncached (start : V) (goal : V) (te : ℕ) :
    astar_heap_lazy_fastpath_cached G hc start goal te
      = astar_heap_lazy_fastpath G heur start goal te := by
  unfold astar_heap_lazy_fastpath_cached
  rw [hc.fn_eq]

/-- **`astar_heap_lazy_fastpath_cached` computes the same result as `astar`.** -/
theorem astar_heap_lazy_fastpath_cached_eq (start : V) (goal : V) (te : ℕ) :
    astar_heap_lazy_fastpath_cached G hc start goal te
      = astar (g := G.toWeightedDiGraph) heur start goal := by
  rw [astar_heap_lazy_fastpath_cached_eq_uncached, astar_heap_lazy_fastpath_eq]

theorem astar_heap_lazy_fastpath_cached_is_sound (start : V) (goal : V) (te : ℕ) :
    (Option.isSome (astar_heap_lazy_fastpath_cached G hc start goal te)
      → (∃ x : ((G.toWeightedDiGraph).Path start goal), x = x)) := by
  rw [astar_heap_lazy_fastpath_cached_eq]
  exact astar_is_sound heur start goal

/-- Completeness of the cached search: identical hypothesis to `astar_is_complete`. -/
theorem astar_heap_lazy_fastpath_cached_is_complete (start : V) (goal : V) (te : ℕ) :
    ((∃ p : ((G.toWeightedDiGraph).Path start goal), ∀ u ∈ p.support, hsearch_expandable heur u)
      → Option.isSome (astar_heap_lazy_fastpath_cached G hc start goal te)) := by
  rw [astar_heap_lazy_fastpath_cached_eq]
  exact astar_is_complete heur start goal

/-- Optimality of the cached search: under an admissible heuristic the returned path is a
cheapest path to the goal. -/
theorem astar_heap_lazy_fastpath_cached_is_optimal (start : V) (goal : V) (te : ℕ)
    (is_admissible : admissible (g := G.toWeightedDiGraph) heur goal)
    (returned_path : Option.isSome (astar_heap_lazy_fastpath_cached G hc start goal te)) :
    ((astar_heap_lazy_fastpath_cached G hc start goal te).get returned_path).is_cheapest := by
  simp only [astar_heap_lazy_fastpath_cached_eq] at returned_path ⊢
  exact astar_is_optimal heur start goal is_admissible returned_path

/-- A\* on the lazily deleted heap (quadratic path reconstruction) with a cached
heuristic. -/
def astar_heap_lazy_cached (start : V) (goal : V) (te : ℕ := 100) :
    Option ((G.toWeightedDiGraph).Path start goal) :=
  astar_heap_lazy G hc.fn start goal te

/-- **`astar_heap_lazy_cached` computes the same result as `astar`.** -/
theorem astar_heap_lazy_cached_eq (start : V) (goal : V) (te : ℕ) :
    astar_heap_lazy_cached G hc start goal te = astar (g := G.toWeightedDiGraph) heur start goal := by
  unfold astar_heap_lazy_cached
  rw [hc.fn_eq, astar_heap_lazy_eq]

/-! ## Multi-goal A\* with a cached heuristic -/

/-- Multi-goal A\* with a lazily deleted heap, linear path reconstruction and a cached
heuristic.  The artificial goal node needs no heuristic value of its own, so the cache of the
real vertices is all that is needed. -/
def astar_multigoal_heap_lazy_fastpath_cached (start : V)
    (is_goal : V → Prop) [DecidablePred is_goal] (te : ℕ := 100) :
    Option ((thegoal : {v : V // is_goal v}) × (G.toWeightedDiGraph).Path start thegoal) :=
  astar_multigoal_heap_lazy_fastpath G hc.fn start is_goal te

/-- The cached multi-goal search computes the same result as the enumeration-based
`astar_multigoal_aux`. -/
theorem astar_multigoal_heap_lazy_fastpath_cached_eq (start : V)
    (is_goal : V → Prop) [DecidablePred is_goal] (te : ℕ) :
    astar_multigoal_heap_lazy_fastpath_cached G hc start is_goal te
      = astar_multigoal_aux (g := G.toWeightedDiGraph) heur start is_goal := by
  unfold astar_multigoal_heap_lazy_fastpath_cached
  rw [hc.fn_eq, astar_multigoal_heap_lazy_fastpath_eq]

theorem astar_multigoal_heap_lazy_fastpath_cached_is_sound (start : V)
    (is_goal : V → Prop) [DecidablePred is_goal] (te : ℕ) :
    (Option.isSome (astar_multigoal_heap_lazy_fastpath_cached G hc start is_goal te) →
      (∃ goal : V, is_goal goal ∧ ∃ x : (G.toWeightedDiGraph).Path start goal, x = x)) := by
  rw [astar_multigoal_heap_lazy_fastpath_cached_eq]
  exact astar_multigoal_aux_is_sound heur start is_goal

theorem astar_multigoal_heap_lazy_fastpath_cached_is_complete (start : V)
    (is_goal : V → Prop) [DecidablePred is_goal] (te : ℕ) :
    ((∃ goal : V, is_goal goal ∧
        ∃ p : (G.toWeightedDiGraph).Path start goal, ∀ u ∈ p.support, heur u ≠ ⊤) →
      Option.isSome (astar_multigoal_heap_lazy_fastpath_cached G hc start is_goal te)) := by
  rw [astar_multigoal_heap_lazy_fastpath_cached_eq]
  exact astar_multigoal_aux_is_complete heur start is_goal

/-- Optimality of the cached multi-goal search. -/
theorem astar_multigoal_heap_lazy_fastpath_cached_is_optimal (start : V)
    (is_goal : V → Prop) [DecidablePred is_goal] (te : ℕ)
    (is_admissible : admissible_pred (g := G.toWeightedDiGraph) heur is_goal)
    (returned_path :
      Option.isSome (astar_multigoal_heap_lazy_fastpath_cached G hc start is_goal te)) :
    ((astar_multigoal_heap_lazy_fastpath_cached G hc start is_goal te).get
      returned_path).2.is_cheapest := by
  revert returned_path
  rw [astar_multigoal_heap_lazy_fastpath_cached_eq]
  exact astar_multigoal_aux_is_optimal heur start is_goal is_admissible

end NatGraph

namespace NatGraph

open WeightedDiGraph
open SearchAlgorithms

variable {V : Type} [FinEnum V] [BEq V] [LawfulBEq V] [Hashable V]
variable (G : NatGraphWithGenerator V) (vi : VIndex V) (heur : V → ℕ∞)

/-! ## Convenience entry points

These build the cache themselves, so one search uses one cache.  Use the versions above when
several searches should share a cache. -/

/-- A\* with the lazily built trie cache of `heur`: the heuristic of a vertex is computed the
first time the search needs it and stored; a vertex that is never touched is never evaluated.
`depth` bounds the number of bits of a vertex number (`64` is unbounded in practice). -/
def astar_heap_lazy_trie (start : V) (goal : V) (depth : ℕ := 64) (te : ℕ := 100) :
    Option ((G.toWeightedDiGraph).Path start goal) :=
  astar_heap_lazy_fastpath_cached G (CachedFun.ofTrie vi depth heur) start goal te

/-- **`astar_heap_lazy_trie` computes the same result as `astar`.** -/
theorem astar_heap_lazy_trie_eq (start : V) (goal : V) (depth : ℕ) (te : ℕ) :
    astar_heap_lazy_trie G vi heur start goal depth te
      = astar (g := G.toWeightedDiGraph) heur start goal :=
  astar_heap_lazy_fastpath_cached_eq G (CachedFun.ofTrie vi depth heur) start goal te

/-- Optimality of `astar_heap_lazy_trie`. -/
theorem astar_heap_lazy_trie_is_optimal (start : V) (goal : V) (depth : ℕ) (te : ℕ)
    (is_admissible : admissible (g := G.toWeightedDiGraph) heur goal)
    (returned_path : Option.isSome (astar_heap_lazy_trie G vi heur start goal depth te)) :
    ((astar_heap_lazy_trie G vi heur start goal depth te).get returned_path).is_cheapest :=
  astar_heap_lazy_fastpath_cached_is_optimal G (CachedFun.ofTrie vi depth heur) start goal te
    is_admissible returned_path

/-- A\* with the lazily built **16-way** trie cache of `heur`: like `astar_heap_lazy_trie`,
but a lookup costs one step per four bits of the vertex number instead of one per bit.
`depth` counts levels; `16` levels cover every vertex number that fits in 64 bits. -/
def astar_heap_lazy_wtrie (start : V) (goal : V) (depth : ℕ := 16) (te : ℕ := 100) :
    Option ((G.toWeightedDiGraph).Path start goal) :=
  astar_heap_lazy_fastpath_cached G (CachedFun.ofWTrie vi depth heur) start goal te

/-- **`astar_heap_lazy_wtrie` computes the same result as `astar`.** -/
theorem astar_heap_lazy_wtrie_eq (start : V) (goal : V) (depth : ℕ) (te : ℕ) :
    astar_heap_lazy_wtrie G vi heur start goal depth te
      = astar (g := G.toWeightedDiGraph) heur start goal :=
  astar_heap_lazy_fastpath_cached_eq G (CachedFun.ofWTrie vi depth heur) start goal te

/-- Optimality of `astar_heap_lazy_wtrie`. -/
theorem astar_heap_lazy_wtrie_is_optimal (start : V) (goal : V) (depth : ℕ) (te : ℕ)
    (is_admissible : admissible (g := G.toWeightedDiGraph) heur goal)
    (returned_path : Option.isSome (astar_heap_lazy_wtrie G vi heur start goal depth te)) :
    ((astar_heap_lazy_wtrie G vi heur start goal depth te).get returned_path).is_cheapest :=
  astar_heap_lazy_fastpath_cached_is_optimal G (CachedFun.ofWTrie vi depth heur) start goal te
    is_admissible returned_path

/-- A\* with the **chunked** cache of `heur`: `nchunks` chunks of `chunk` thunks, each chunk
allocated only when a vertex in it is first looked up.  Two array indexings per lookup, and
memory proportional to the chunks the search touches. -/
def astar_heap_lazy_chunked (chunk nchunks : ℕ) (start : V) (goal : V) (te : ℕ := 100) :
    Option ((G.toWeightedDiGraph).Path start goal) :=
  astar_heap_lazy_fastpath_cached G (CachedFun.ofChunked chunk nchunks vi heur) start goal te

/-- **`astar_heap_lazy_chunked` computes the same result as `astar`.** -/
theorem astar_heap_lazy_chunked_eq (chunk nchunks : ℕ) (start : V) (goal : V) (te : ℕ) :
    astar_heap_lazy_chunked G vi heur chunk nchunks start goal te
      = astar (g := G.toWeightedDiGraph) heur start goal :=
  astar_heap_lazy_fastpath_cached_eq G (CachedFun.ofChunked chunk nchunks vi heur) start goal te

/-- Optimality of `astar_heap_lazy_chunked`. -/
theorem astar_heap_lazy_chunked_is_optimal (chunk nchunks : ℕ) (start : V) (goal : V) (te : ℕ)
    (is_admissible : admissible (g := G.toWeightedDiGraph) heur goal)
    (returned_path :
      Option.isSome (astar_heap_lazy_chunked G vi heur chunk nchunks start goal te)) :
    ((astar_heap_lazy_chunked G vi heur chunk nchunks start goal te).get
      returned_path).is_cheapest :=
  astar_heap_lazy_fastpath_cached_is_optimal G (CachedFun.ofChunked chunk nchunks vi heur)
    start goal te is_admissible returned_path

/-- A\* with the flat array cache of `heur`: `n` unevaluated thunks, one per vertex number,
`O(1)` per lookup.  Each `heur v` is still evaluated at most once, and only if the search
looks at `v`. -/
def astar_heap_lazy_array (n : ℕ) (start : V) (goal : V) (te : ℕ := 100) :
    Option ((G.toWeightedDiGraph).Path start goal) :=
  astar_heap_lazy_fastpath_cached G (CachedFun.ofArray n vi heur) start goal te

/-- **`astar_heap_lazy_array` computes the same result as `astar`.** -/
theorem astar_heap_lazy_array_eq (n : ℕ) (start : V) (goal : V) (te : ℕ) :
    astar_heap_lazy_array G vi heur n start goal te
      = astar (g := G.toWeightedDiGraph) heur start goal :=
  astar_heap_lazy_fastpath_cached_eq G (CachedFun.ofArray n vi heur) start goal te

/-- Optimality of `astar_heap_lazy_array`. -/
theorem astar_heap_lazy_array_is_optimal (n : ℕ) (start : V) (goal : V) (te : ℕ)
    (is_admissible : admissible (g := G.toWeightedDiGraph) heur goal)
    (returned_path : Option.isSome (astar_heap_lazy_array G vi heur n start goal te)) :
    ((astar_heap_lazy_array G vi heur n start goal te).get returned_path).is_cheapest :=
  astar_heap_lazy_fastpath_cached_is_optimal G (CachedFun.ofArray n vi heur) start goal te
    is_admissible returned_path

end NatGraph
