import Mathlib.Data.Nat.Basic

/-!
# Lazy, memoising caches for pure functions

The heuristic of a heuristic search is a **pure function**: `heur v` has the same value every
time it is asked for.  The searches of this library ask for it a lot — once per neighbour in
every expansion, and, because the queue is ordered by the `f`-value, `O(log m)` times per
queue operation.  If evaluating the heuristic is expensive (a pattern database, a relaxed
sub-search, distances to a set of landmarks, …) then this, and not the queue, is what a
search spends its time on.

This module provides the data structure that fixes it: a cache that evaluates the cached
function **at most once per argument**, is completely pure, and is *provably* the function it
caches — so no correctness proof of any search has to change (see
`SearchAlgorithms.HeuristicCache`).

## How it works

`Thunk α` is Lean's lazy value: `Thunk.get` runs the closure the first time and **stores the
result in the thunk object**, so every later `get` on the same object returns the stored
value without running anything.  A cache is therefore a data structure of thunks that is
created once and shared by all the calls.

`HTrie` is a binary trie over the natural numbers of which *only the nodes actually visited
are ever built*: the value of a node and its two subtries are all thunks.  Building the cache
costs `O(1)`, a lookup of index `i` costs `O(log i)` pointer hops, and the memory used is
proportional to the number of *distinct arguments looked up* (times `log`), not to the size
of the vertex type.  This is what a search on a huge vertex type that only touches a small
part of it needs.  `SearchAlgorithms.HeuristicCache` also offers a flat
`Array (Thunk α)` variant with `O(1)` lookup for the case where the vertex type is small
enough to allocate one cell per vertex.

Neither ever evaluates the cached function more than once per argument, and neither
evaluates it at all for an argument that is never looked up.
-/

universe u

namespace SearchAlgorithms

/-- A lazily built binary trie over `ℕ`.  A node carries the value of index `0` and the two
subtries for the odd and the even positive indices; **all three are thunks**, so the tree is
only built along the paths that are looked up, and each node is built at most once. -/
inductive HTrie (α : Type u) where
  /-- The empty trie: every lookup misses. -/
  | leaf : HTrie α
  /-- A node: the value at index `0`, the subtrie of the indices `2k+1` and the subtrie of
  the indices `2k+2`. -/
  | node (val : Thunk α) (l r : Thunk (HTrie α)) : HTrie α

namespace HTrie

variable {α : Type u}

/-- The trie of depth `d` for the function `g`: the node reached by the index `m` (for
`m + 1 < 2 ^ d`) holds `g m`.  Building it costs `O(1)`: only the root node is allocated,
everything below it is an unevaluated thunk.  `d` bounds the number of *bits* of an index, so
`d = 64` is unbounded for all practical purposes. -/
def build (d : ℕ) (g : ℕ → α) : HTrie α :=
  match d with
  | 0 => .leaf
  | d + 1 =>
    .node (Thunk.mk fun _ => g 0)
      (Thunk.mk fun _ => build d fun k => g (2 * k + 1))
      (Thunk.mk fun _ => build d fun k => g (2 * k + 2))

/-- Look up index `m`.  This forces one thunk per bit of `m`; each of them is evaluated at
most once over the whole life of the trie. -/
def get (t : HTrie α) (m : ℕ) : Option α :=
  match t with
  | .leaf => none
  | .node v l r =>
    match m with
    | 0 => some v.get
    | m + 1 => if m % 2 = 0 then get l.get (m / 2) else get r.get (m / 2)

@[simp] theorem get_leaf (m : ℕ) : (leaf : HTrie α).get m = none := by simp [get]

@[simp] theorem get_node_zero (v : Thunk α) (l r : Thunk (HTrie α)) :
    (node v l r).get 0 = some v.get := by simp [get]

theorem get_node_succ (v : Thunk α) (l r : Thunk (HTrie α)) (m : ℕ) :
    (node v l r).get (m + 1) = if m % 2 = 0 then get l.get (m / 2) else get r.get (m / 2) := by
  simp [get]

theorem build_zero (g : ℕ → α) : build 0 g = leaf := rfl

theorem build_succ (d : ℕ) (g : ℕ → α) :
    build (d + 1) g = node (Thunk.mk fun _ => g 0)
      (Thunk.mk fun _ => build d fun k => g (2 * k + 1))
      (Thunk.mk fun _ => build d fun k => g (2 * k + 2)) := rfl

/-- Looking up an odd index descends into the left subtrie. -/
theorem get_build_succ_even (d : ℕ) (g : ℕ → α) (m : ℕ) (hm : m % 2 = 0) :
    (build (d + 1) g).get (m + 1) = (build d fun k => g (2 * k + 1)).get (m / 2) := by
  rw [build_succ, get_node_succ, if_pos hm]
  rfl

/-- Looking up an even positive index descends into the right subtrie. -/
theorem get_build_succ_odd (d : ℕ) (g : ℕ → α) (m : ℕ) (hm : ¬ m % 2 = 0) :
    (build (d + 1) g).get (m + 1) = (build d fun k => g (2 * k + 2)).get (m / 2) := by
  rw [build_succ, get_node_succ, if_neg hm]
  rfl

/-- **Soundness of the cache**: a lookup either misses (the index has more bits than the
depth of the trie) or returns the value of the cached function at *that* index.  Nothing is
assumed about `g`, and in particular no bound on `m` is needed. -/
theorem get_build_eq_or_none (d : ℕ) (g : ℕ → α) (m : ℕ) :
    (build d g).get m = none ∨ (build d g).get m = some (g m) := by
  induction m using Nat.strongRecOn generalizing d g with
  | _ m ih =>
    match d with
    | 0 => exact Or.inl (by simp [build_zero])
    | d + 1 =>
      match m with
      | 0 => exact Or.inr (by rw [build_succ, get_node_zero]; rfl)
      | m + 1 =>
        by_cases hm : m % 2 = 0
        · have hidx : 2 * (m / 2) + 1 = m + 1 := by omega
          rcases ih (m / 2) (by omega) d (fun k => g (2 * k + 1)) with h' | h'
          · exact Or.inl (by rw [get_build_succ_even d g m hm, h'])
          · refine Or.inr ?_
            rw [get_build_succ_even d g m hm, h']
            simp only [hidx]
        · have hidx : 2 * (m / 2) + 2 = m + 1 := by omega
          rcases ih (m / 2) (by omega) d (fun k => g (2 * k + 2)) with h' | h'
          · exact Or.inl (by rw [get_build_succ_odd d g m hm, h'])
          · refine Or.inr ?_
            rw [get_build_succ_odd d g m hm, h']
            simp only [hidx]

/-- **Completeness of the cache**: a lookup of an index with fewer than `d` bits hits. -/
theorem get_build (d : ℕ) (g : ℕ → α) (m : ℕ) (h : m + 1 < 2 ^ d) :
    (build d g).get m = some (g m) := by
  induction m using Nat.strongRecOn generalizing d g with
  | _ m ih =>
    match d with
    | 0 => simp at h
    | d + 1 =>
      have hpow : 2 ^ (d + 1) = 2 * 2 ^ d := by rw [Nat.pow_succ]; omega
      match m with
      | 0 => rw [build_succ, get_node_zero]; rfl
      | m + 1 =>
        by_cases hm : m % 2 = 0
        · have hidx : 2 * (m / 2) + 1 = m + 1 := by omega
          have hlt : m / 2 + 1 < 2 ^ d := by omega
          rw [get_build_succ_even d g m hm, ih (m / 2) (by omega) d (fun k => g (2 * k + 1)) hlt]
          simp only [hidx]
        · have hidx : 2 * (m / 2) + 2 = m + 1 := by omega
          have hlt : m / 2 + 1 < 2 ^ d := by omega
          rw [get_build_succ_odd d g m hm, ih (m / 2) (by omega) d (fun k => g (2 * k + 2)) hlt]
          simp only [hidx]

end HTrie

/-!
## The 16-way trie

The binary trie needs one thunk force and one step of arithmetic per *bit* of the index —
fourteen levels for a graph with ten thousand vertices.  `WTrie` is the same construction
with sixteen children per node, i.e. four bits per level, so a lookup is about four times
cheaper.  It allocates sixteen (unevaluated) child thunks per *visited* node instead of two,
which is still proportional to the part of the graph the search touches.
-/

/-- A lazily built 16-way trie over `ℕ`: a node carries the value of index `0` and sixteen
subtries, all of them thunks, so only the nodes that are looked up are ever built. -/
inductive WTrie (α : Type u) where
  /-- The empty trie: every lookup misses. -/
  | leaf : WTrie α
  /-- A node: the value at index `0` and the sixteen subtries of the positive indices,
  distributed by the remainder of `index - 1` modulo `16`. -/
  | node (val : Thunk α) (kids : Array (Thunk (WTrie α))) : WTrie α

namespace WTrie

variable {α : Type u}

/-- The 16-way trie of depth `d` for `g`: the node reached by the index `m` (for
`m + 1 < 16 ^ d`) holds `g m`.  Building it costs `O(1)`. -/
def build (d : ℕ) (g : ℕ → α) : WTrie α :=
  match d with
  | 0 => .leaf
  | d + 1 =>
    .node (Thunk.mk fun _ => g 0)
      (Array.ofFn (n := 16) fun j => Thunk.mk fun _ => build d fun k => g (16 * k + j.val + 1))

/-- Look up index `m`: one thunk force and one division per four bits of `m`. -/
def get (t : WTrie α) (m : ℕ) : Option α :=
  match t with
  | .leaf => none
  | .node v kids =>
    match m with
    | 0 => some v.get
    | m + 1 =>
      match kids[m % 16]? with
      | some c => get c.get (m / 16)
      | none => none

theorem build_succ (d : ℕ) (g : ℕ → α) :
    build (d + 1) g = node (Thunk.mk fun _ => g 0)
      (Array.ofFn (n := 16) fun j =>
        Thunk.mk fun _ => build d fun k => g (16 * k + j.val + 1)) := rfl

@[simp] theorem get_leaf (m : ℕ) : (leaf : WTrie α).get m = none := by simp [get]

@[simp] theorem get_node_zero (v : Thunk α) (kids : Array (Thunk (WTrie α))) :
    (node v kids).get 0 = some v.get := by simp [get]

theorem get_node_succ (v : Thunk α) (kids : Array (Thunk (WTrie α))) (m : ℕ) :
    (node v kids).get (m + 1) =
      match kids[m % 16]? with
      | some c => get c.get (m / 16)
      | none => none := by
  simp [get]

/-- A lookup of a positive index descends into the subtrie selected by the low four bits. -/
theorem get_build_succ (d : ℕ) (g : ℕ → α) (m : ℕ) :
    (build (d + 1) g).get (m + 1)
      = (build d fun k => g (16 * k + m % 16 + 1)).get (m / 16) := by
  have h16 : m % 16 < 16 := Nat.mod_lt _ (by omega)
  rw [build_succ, get_node_succ]
  rw [Array.getElem?_eq_getElem (by simpa using h16)]
  simp only [Array.getElem_ofFn]
  rfl

/-- **Soundness**: a lookup either misses or returns the value of the cached function at that
index. -/
theorem get_build_eq_or_none (d : ℕ) (g : ℕ → α) (m : ℕ) :
    (build d g).get m = none ∨ (build d g).get m = some (g m) := by
  induction m using Nat.strongRecOn generalizing d g with
  | _ m ih =>
    match d with
    | 0 => exact Or.inl (by simp [build])
    | d + 1 =>
      match m with
      | 0 => exact Or.inr (by rw [build_succ, get_node_zero]; rfl)
      | m + 1 =>
        have hidx : 16 * (m / 16) + m % 16 + 1 = m + 1 := by omega
        rcases ih (m / 16) (by omega) d (fun k => g (16 * k + m % 16 + 1)) with h' | h'
        · exact Or.inl (by rw [get_build_succ d g m, h'])
        · refine Or.inr ?_
          rw [get_build_succ d g m, h']
          simp only [hidx]

/-- **Completeness**: a trie of depth `d` holds the indices below `(16 ^ d - 1) / 15`, i.e.
those with fewer than `4 * d` bits. -/
theorem get_build (d : ℕ) (g : ℕ → α) (m : ℕ) (h : 15 * m + 1 < 16 ^ d) :
    (build d g).get m = some (g m) := by
  induction m using Nat.strongRecOn generalizing d g with
  | _ m ih =>
    match d with
    | 0 => simp only [Nat.pow_zero] at h; omega
    | d + 1 =>
      have hpow : 16 ^ (d + 1) = 16 * 16 ^ d := by rw [Nat.pow_succ]; omega
      match m with
      | 0 => rw [build_succ, get_node_zero]; rfl
      | m + 1 =>
        have hidx : 16 * (m / 16) + m % 16 + 1 = m + 1 := by omega
        have hlt : 15 * (m / 16) + 1 < 16 ^ d := by omega
        rw [get_build_succ d g m,
          ih (m / 16) (by omega) d (fun k => g (16 * k + m % 16 + 1)) hlt]
        simp only [hidx]

end WTrie

end SearchAlgorithms
