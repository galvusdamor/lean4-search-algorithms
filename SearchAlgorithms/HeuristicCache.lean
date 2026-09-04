import SearchAlgorithms.LazyMemo
import Mathlib.Data.FinEnum
import Mathlib.Data.ENat.Basic

/-!
# Caching the heuristic

The heuristic of a heuristic search is a **pure function of the vertex**: `heur v` cannot
change during a search, so it only ever has to be computed once per vertex.  The searches of
this library nevertheless call it very often:

* once per neighbour of every expanded node (the test `heur v ≠ ⊤`), and
* inside the queue comparator, which computes the `f`-value `pathOrder v + heur v` of both
  arguments — that is `O(log m)` calls per heap operation and hence a multiple of
  `deg · log m` calls per expansion.

If evaluating the heuristic is expensive, this — not the queue — is what a search spends its
time on.

This module turns any pure `f : V → α` into a **memoising** version of itself:

```lean
let hc := CachedFun.ofChunked 1024 (n / 1024 + 1) (VIndex.ofFin n) heur
astar_heap_lazy_fastpath_cached G hc start goal
```

`hc.fn` evaluates `heur v` at most once for each `v` — the first time it is asked — and
returns the stored value afterwards; a vertex that is never looked at is never evaluated.
The cache is a structure of `Thunk`s created once (see `SearchAlgorithms.LazyMemo`), so it is
shared by every call of `hc.fn` and there is no state to thread through the search.

**No correctness proof changes.**  `CachedFun` carries the proof `fn_eq : fn = f`: the cached
function is *literally the same function*, so every theorem about a search run with `heur`
holds verbatim for the search run with `hc.fn` (`CachedFun.apply_eq`).  The searches with a
cached heuristic are defined in `SearchAlgorithms.AStarCached`, together with the equations
that say they return the same path as `astar`.

## What the cache is indexed by

A `VIndex V` is an injective numbering `idx : V → ℕ` of the vertices together with a partial
inverse.  For `V = Fin n` it is `Fin.val` (`VIndex.ofFin`), which costs nothing; for a general
`FinEnum` type `VIndex.ofFinEnum` uses the enumeration, which may be slow (for the enumeration
built from a list it is a linear search), so prefer a hand-written index when there is one.
`VIndex.option` lifts an index to `Option V`, the vertex type used by the multi-goal searches.

Three cache shapes are offered:

* `CachedFun.ofTrie vi depth f` — the lazily built trie of `SearchAlgorithms.LazyMemo`:
  creating it is `O(1)`, a lookup costs `O(log (idx v))` pointer hops, and the memory used is
  proportional to the number of *distinct* vertices looked up.  `depth` bounds the number of
  bits of an index (`64` is unbounded in practice); an index that does not fit simply misses
  the cache and is recomputed, so the result is correct whatever `depth` is.
* `CachedFun.ofChunked chunk nchunks vi f` — an array of `nchunks` chunks of `chunk`
  unevaluated thunks, each chunk allocated when a vertex in it is first looked up: two array
  indexings per lookup (measured about as fast as the flat array) and memory only for the
  chunks the search touches.  The best default when the vertex numbers are dense.
* `CachedFun.ofArray n vi f` — a flat `Array` of `n` unevaluated thunks: `O(1)` lookup, but
  one cell per vertex is allocated up front.  Use it when `n` is small enough and the search
  touches a large part of the graph.

Neither ever evaluates `f` twice on the same argument.
-/

namespace SearchAlgorithms

universe u

variable {V : Type} {α : Type u}

/-! ## Numbering the vertices -/

/-- An injective numbering of `V` by natural numbers, with a partial inverse.  This is what a
cache is indexed by; the numbering should be cheap to compute (`Fin.val`, a field of a record,
a packed board position, …). -/
structure VIndex (V : Type) where
  /-- The number of a vertex. -/
  idx : V → ℕ
  /-- The vertex of a number, if there is one. -/
  ofIdx : ℕ → Option V
  /-- `ofIdx` inverts `idx`.  In particular `idx` is injective. -/
  ofIdx_idx : ∀ v, ofIdx (idx v) = some v

/-- The identity numbering of `Fin n`. -/
def VIndex.ofFin (n : ℕ) : VIndex (Fin n) where
  idx v := v.val
  ofIdx m := if h : m < n then some ⟨m, h⟩ else none
  ofIdx_idx v := by simp

/-- The identity numbering of `ℕ` (for graphs whose vertices are natural numbers). -/
def VIndex.ofNat : VIndex ℕ where
  idx v := v
  ofIdx m := some m
  ofIdx_idx _ := rfl

/-- The numbering coming from a `FinEnum` instance.  Convenient but not always cheap: for the
instance built from a list, `FinEnum.equiv` is a linear search, in which case a hand-written
`VIndex` is much faster. -/
def VIndex.ofFinEnum (V : Type) [FinEnum V] : VIndex V where
  idx v := (FinEnum.equiv v).val
  ofIdx m := if h : m < FinEnum.card V then some (FinEnum.equiv.symm ⟨m, h⟩) else none
  ofIdx_idx v := by simp

/-- Lift a numbering to `Option V`, the vertex type of the graph with an artificial goal node
that the multi-goal searches run on. -/
def VIndex.option (vi : VIndex V) : VIndex (Option V) where
  idx v := match v with | none => 0 | some v => vi.idx v + 1
  ofIdx m := match m with | 0 => some none | m + 1 => (vi.ofIdx m).map some
  ofIdx_idx v := by cases v with
    | none => rfl
    | some v => simp [vi.ofIdx_idx v]

/-! ## Cached functions -/

/-- A **cached version of the pure function `f`**: a function `fn` that computes the same
values, together with the proof that it *is* `f`.  Everything proved about a search run with
`f` therefore holds for the search run with `fn`; only the run time differs. -/
structure CachedFun {V : Type} {α : Type u} (f : V → α) where
  /-- The cached function. -/
  fn : V → α
  /-- It is the function it caches. -/
  fn_eq : fn = f

/-- Anything applied to a cached function is what it is applied to the function itself.  This
is how the correctness statements of the searches are transferred. -/
theorem CachedFun.apply_eq {β : Sort*} {f : V → α} (c : CachedFun f) (F : (V → α) → β) :
    F c.fn = F f := by rw [c.fn_eq]

/-- The trivial cache: no caching at all. -/
def CachedFun.id (f : V → α) : CachedFun f := ⟨f, rfl⟩

/-! ### The lazily built trie cache -/

/-- Look `v` up in a trie cache; on a miss (an index too long for the depth of the trie)
compute `f v`.  `f v` is only evaluated in the miss branch. -/
def trieLookup (vi : VIndex V) (t : HTrie (Option α)) (f : V → α) (v : V) : α :=
  match t.get (vi.idx v) with
  | some (some x) => x
  | _ => f v

/-- The trie cache of `f`: the value at index `n` is `f` of the vertex numbered `n`. -/
def trieOf (vi : VIndex V) (depth : ℕ) (f : V → α) : HTrie (Option α) :=
  HTrie.build depth fun n => (vi.ofIdx n).map f

theorem trieLookup_eq (vi : VIndex V) (depth : ℕ) (f : V → α) :
    trieLookup vi (trieOf vi depth f) f = f := by
  funext v
  unfold trieLookup trieOf
  rcases HTrie.get_build_eq_or_none depth (fun n => (vi.ofIdx n).map f) (vi.idx v) with h | h <;>
    rw [h]
  simp [vi.ofIdx_idx v]

/-- **The lazily built cache of `f`.**  Creating it is `O(1)` — the trie is a single node
whose children are unevaluated thunks — a lookup costs `O(log (idx v))` pointer hops, and
`f v` is evaluated at most once for each `v`, the first time it is looked up.  `depth` bounds
the number of bits of a vertex number; `64` is unbounded in practice, and a vertex whose
number does not fit is simply not cached. -/
def CachedFun.ofTrie (vi : VIndex V) (depth : ℕ) (f : V → α) : CachedFun f :=
  ⟨trieLookup vi (trieOf vi depth f) f, trieLookup_eq vi depth f⟩

/-! ### The 16-way trie cache -/

/-- Look `v` up in a 16-way trie cache; on a miss compute `f v`.  `f v` is only evaluated in
the miss branch. -/
def wtrieLookup (vi : VIndex V) (t : WTrie (Option α)) (f : V → α) (v : V) : α :=
  match t.get (vi.idx v) with
  | some (some x) => x
  | _ => f v

/-- The 16-way trie cache of `f`. -/
def wtrieOf (vi : VIndex V) (depth : ℕ) (f : V → α) : WTrie (Option α) :=
  WTrie.build depth fun n => (vi.ofIdx n).map f

theorem wtrieLookup_eq (vi : VIndex V) (depth : ℕ) (f : V → α) :
    wtrieLookup vi (wtrieOf vi depth f) f = f := by
  funext v
  unfold wtrieLookup wtrieOf
  rcases WTrie.get_build_eq_or_none depth (fun n => (vi.ofIdx n).map f) (vi.idx v) with h | h <;>
    rw [h]
  simp [vi.ofIdx_idx v]

/-- **The lazily built 16-way cache of `f`** — the default choice.  Like `CachedFun.ofTrie`,
but with sixteen children per node, so a lookup costs one thunk force per *four* bits of the
vertex number instead of one per bit.  `depth` counts levels, so `16` levels cover every
vertex number below `(16 ^ 16 - 1) / 15`. -/
def CachedFun.ofWTrie (vi : VIndex V) (depth : ℕ) (f : V → α) : CachedFun f :=
  ⟨wtrieLookup vi (wtrieOf vi depth f) f, wtrieLookup_eq vi depth f⟩

/-! ### The flat array cache -/

/-- Look `v` up in an array cache; on a miss (a vertex number beyond the array) compute
`f v`.  `f v` is only evaluated in the miss branch. -/
def arrayLookup (vi : VIndex V) (a : Array (Thunk (Option α))) (f : V → α) (v : V) : α :=
  match a[vi.idx v]? with
  | some t => match t.get with
    | some x => x
    | none => f v
  | none => f v

/-- The array cache of `f`: `n` unevaluated thunks, one per vertex number. -/
def arrayOf (n : ℕ) (vi : VIndex V) (f : V → α) : Array (Thunk (Option α)) :=
  Array.ofFn (n := n) fun i => Thunk.mk fun _ => (vi.ofIdx i.val).map f

theorem arrayLookup_eq (n : ℕ) (vi : VIndex V) (f : V → α) :
    arrayLookup vi (arrayOf n vi f) f = f := by
  funext v
  unfold arrayLookup arrayOf
  by_cases h : vi.idx v < n
  · rw [Array.getElem?_eq_getElem (by simpa using h)]
    simp only [Array.getElem_ofFn, vi.ofIdx_idx v, Option.map_some]
    rfl
  · rw [Array.getElem?_eq_none (by simpa using h)]

/-- **The flat cache of `f`**: an array of `n` unevaluated thunks, `O(1)` per lookup.  `f v`
is evaluated at most once for each `v`, the first time it is looked up; a vertex whose number
is at least `n` is not cached. -/
def CachedFun.ofArray (n : ℕ) (vi : VIndex V) (f : V → α) : CachedFun f :=
  ⟨arrayLookup vi (arrayOf n vi f) f, arrayLookup_eq n vi f⟩

/-! ### The chunked cache -/

/-- Look `v` up in a chunked cache: one array indexing to find the chunk (which is allocated
when it is first used) and one inside it.  On a miss compute `f v`. -/
def chunkedLookup (chunk : ℕ) (vi : VIndex V)
    (a : Array (Thunk (Array (Thunk (Option α))))) (f : V → α) (v : V) : α :=
  match a[vi.idx v / chunk]? with
  | some t => match (t.get)[vi.idx v % chunk]? with
    | some u => match u.get with
      | some x => x
      | none => f v
    | none => f v
  | none => f v

/-- The chunked cache of `f`: `nchunks` unevaluated chunks of `chunk` unevaluated thunks. -/
def chunkedOf (chunk nchunks : ℕ) (vi : VIndex V) (f : V → α) :
    Array (Thunk (Array (Thunk (Option α)))) :=
  Array.ofFn (n := nchunks) fun c => Thunk.mk fun _ =>
    Array.ofFn (n := chunk) fun j => Thunk.mk fun _ => (vi.ofIdx (c.val * chunk + j.val)).map f

theorem chunkedLookup_eq (chunk nchunks : ℕ) (vi : VIndex V) (f : V → α) :
    chunkedLookup chunk vi (chunkedOf chunk nchunks vi f) f = f := by
  funext v
  unfold chunkedLookup chunkedOf
  by_cases h1 : vi.idx v / chunk < nchunks
  · rw [Array.getElem?_eq_getElem (by simpa using h1)]
    simp only [Array.getElem_ofFn]
    by_cases h2 : vi.idx v % chunk < chunk
    · show (match (Array.ofFn (n := chunk) fun j =>
          Thunk.mk fun _ => (vi.ofIdx (vi.idx v / chunk * chunk + j.val)).map f)[
            vi.idx v % chunk]? with
        | some u => match u.get with
          | some x => x
          | none => f v
        | none => f v) = f v
      rw [Array.getElem?_eq_getElem (by simpa using h2)]
      simp only [Array.getElem_ofFn,
        Nat.div_add_mod' (vi.idx v) chunk,
        vi.ofIdx_idx v, Option.map_some]
      rfl
    · show (match (Array.ofFn (n := chunk) fun j =>
          Thunk.mk fun _ => (vi.ofIdx (vi.idx v / chunk * chunk + j.val)).map f)[
            vi.idx v % chunk]? with
        | some u => match u.get with
          | some x => x
          | none => f v
        | none => f v) = f v
      rw [Array.getElem?_eq_none (by simpa using h2)]
  · rw [Array.getElem?_eq_none (by simpa using h1)]

/-- **The chunked cache of `f`**: an array of `nchunks` chunks, each of which is an array of
`chunk` unevaluated thunks that is itself only allocated when a vertex in it is first looked
up.  A lookup is two array indexings, and the memory used is proportional to the number of
chunks the search touches — the compromise between `CachedFun.ofArray` (fastest, one cell per
vertex) and `CachedFun.ofWTrie` (least memory, slowest).  Vertex numbers at least
`chunk * nchunks` are not cached. -/
def CachedFun.ofChunked (chunk nchunks : ℕ) (vi : VIndex V) (f : V → α) : CachedFun f :=
  ⟨chunkedLookup chunk vi (chunkedOf chunk nchunks vi f) f, chunkedLookup_eq chunk nchunks vi f⟩

/-! ## Caching a heuristic -/

/-- A cached heuristic: the same function as `heur`, evaluated at most once per vertex. -/
abbrev CachedHeuristic (V : Type) (heur : V → ℕ∞) := CachedFun heur

/-- The cached heuristic of the graph with an artificial goal node, on which the multi-goal
searches run.  `opt_heur heur` maps the artificial node to `0` and every real vertex to its
(cached) heuristic value, so nothing has to be cached twice. -/
def CachedFun.optionMap {heur : V → ℕ∞} (c : CachedHeuristic V heur)
    (optH : (V → ℕ∞) → (Option V → ℕ∞)) : CachedHeuristic (Option V) (optH heur) :=
  ⟨optH c.fn, by rw [c.fn_eq]⟩

end SearchAlgorithms
