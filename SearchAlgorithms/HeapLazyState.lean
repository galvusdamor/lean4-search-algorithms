import SearchAlgorithms.HeuristicSearchHeap
import SearchAlgorithms.StaleQueue
import SearchAlgorithms.LazyAux

/-!
# Heuristic search with a lazily-deleted heap (`heap_lazy`)

`SearchAlgorithms.HeuristicSearchHeap` keeps the search queue in a leftist heap ordered by the
*current* path order of its entries.  That makes queueing a node `O(log m)`, but it has one
expensive case left: when an expansion improves the path order of a node that is still in the
queue (a **decrease-key**), the comparison function changes, the heap invariant may break, and
the queue has to be rebuilt — `Θ(m log m)` for a queue of `m` nodes.  Decrease-key is not a
rare event (it is what Dijkstra's relaxation does), so a search whose queue is large pays this
on many expansions.

This module is a *new* implementation — nothing in the existing ones is changed — which
removes that case by **lazy deletion**:

* every heap entry is a pair `((v, key), n)`: the vertex, **the path order `v` had when the
  entry was created**, and the number of the insertion that created it.  The comparison
  function reads the stored `key`, never the path-order map, so it never changes: the heap
  invariant cannot be broken by an update of the path order and the heap is never rebuilt.
* a decrease-key simply **inserts a new entry** (`O(log m)`) and leaves the old one in the
  heap, where it becomes *stale*;
* `queued : Std.HashMap V ℕ` remembers, for every vertex in the queue, the number of its
  current entry.  An entry is **live** iff `queued[v] = n`; everything else is stale.
* stale entries are dropped when they arrive at the root (`HeapQueue.purge`), which costs
  `O(log m)` and happens at most once per entry.

So *every* expansion is `O(deg · log m)`, whatever the path orders do.

## Correctness

Exactly as for the other implementations, nothing is re-proved: the abstract state after each
expansion is shown to be the state of the reference implementation, and soundness,
completeness and optimality then transfer (see `SearchAlgorithms.AStarHeapLazy`).

The queue represented by the state is `HeapQueue.liveQueue`, the entries in queue order with
the stale ones removed, and the core lemma `HeapQueue.liveQueue_eq`
(`SearchAlgorithms.StaleQueue`) says that this is the *stable sort* of the live entries: the
stale entries are invisible.  Because the reference implementation sorts with the **stable**
`List.mergeSort`, the numbers of the live entries have to reproduce its tie-breaking; the
delicate point is the decrease-key:

* a re-inserted node gets a **fresh** number, so it sorts *after* every node it is now tied
  with — which is correct, because a node it is tied with after the decrease had a strictly
  smaller `f`-value before, hence stood before it in the queue;
* several nodes re-inserted by the *same* expansion are inserted **in queue order** (the list
  is sorted by their old entries first, `O(deg log deg)`), so their relative order is the one
  the reference sort would give them.

`hsearch_lazy_D_ref_tie` is where these two facts are proved.

## Instrumentation

The state carries a counter of expansions and a `traceEvery` field: if it is non-zero, every
`traceEvery`-th expansion prints one line on stderr with the number of nodes expanded so far,
the size of the queue, the number of visited nodes and the number of heap insertions made.
Printing is done with `dbg_trace`, which is the identity function (`traceIf_eq`), so the
traced search is *literally* the same function as the untraced one and no proof is affected.
-/

namespace NatGraph

open WeightedDiGraph
open SearchAlgorithms

variable {V : Type} [FinEnum V] [BEq V] [LawfulBEq V] [Hashable V]

/-!
## Printing progress
-/

/-- Print `msg ()` on stderr if `b`, and return `a`.  This is the identity function
(`traceIf_eq`): `dbg_trace` is `fun _ f => f ()`. -/
@[inline] def traceIf {α : Type} (b : Bool) (msg : Unit → String) (a : α) : α :=
  if b then dbg_trace (msg ()); a else a

theorem traceIf_eq {α : Type} (b : Bool) (msg : Unit → String) (a : α) : traceIf b msg a = a := by
  unfold traceIf
  split <;> rfl

/-!
## Queue entries and the comparison function
-/

/-- What the queue is sorted by: a vertex together with the path order it was queued with. -/
abbrev LazyKey (V : Type) := V × (ℕ × ℕ)

/-- A queue entry: a `LazyKey` decorated with the number of the insertion that created it.
The number is unique, and among the *live* entries it is the tie-breaking rank of the
reference implementation's stable sort. -/
abbrev LazyEntry (V : Type) := LazyKey V × ℕ

/-- The order on queue entries: by the `f`-value computed from the **stored** path order.
It does not depend on the state, so no update of the path order can break the heap. -/
def hsearch_lazy_key_le (heur : V → ℕ∞) (a b : LazyKey V) : Bool :=
  add_heur a.1 a.2 heur = add_heur b.1 b.2 heur ||
    FValueComp.lt (add_heur a.1 a.2 heur) (add_heur b.1 b.2 heur)

omit [FinEnum V] [BEq V] [LawfulBEq V] [Hashable V] in
theorem hsearch_lazy_key_le_trans (heur : V → ℕ∞) (a b c : LazyKey V) :
    hsearch_lazy_key_le heur a b → hsearch_lazy_key_le heur b c → hsearch_lazy_key_le heur a c :=
  hsearch_merge_trans _ _ _

omit [FinEnum V] [BEq V] [LawfulBEq V] [Hashable V] in
theorem hsearch_lazy_key_le_total (heur : V → ℕ∞) (a b : LazyKey V) :
    (hsearch_lazy_key_le heur a b || hsearch_lazy_key_le heur b a) = true :=
  hsearch_merge_total _ _

omit [FinEnum V] [BEq V] [LawfulBEq V] [Hashable V] in
/-- On entries carrying the current path order, the entry order is the queue order of the
reference implementation. -/
theorem hsearch_lazy_key_le_eq (heur : V → ℕ∞) (o : V → ℕ × ℕ) (a b : V) :
    hsearch_lazy_key_le heur (a, o a) (b, o b) = hsearch_queue_le heur o a b := rfl

/-- The order the heap is kept in: by `f`-value of the stored key, ties broken by the
insertion number. -/
abbrev hsearch_lazy_le (heur : V → ℕ∞) : LazyEntry V → LazyEntry V → Bool :=
  List.zipIdxLE (hsearch_lazy_key_le heur)

omit [FinEnum V] [BEq V] [LawfulBEq V] [Hashable V] in
theorem hsearch_lazy_le_trans (heur : V → ℕ∞) (a b c : LazyEntry V) :
    hsearch_lazy_le heur a b → hsearch_lazy_le heur b c → hsearch_lazy_le heur a c :=
  List.zipIdxLE_trans (hsearch_lazy_key_le_trans heur) a b c

omit [FinEnum V] [BEq V] [LawfulBEq V] [Hashable V] in
theorem hsearch_lazy_le_total (heur : V → ℕ∞) (a b : LazyEntry V) :
    (hsearch_lazy_le heur a b || hsearch_lazy_le heur b a) = true :=
  List.zipIdxLE_total (hsearch_lazy_key_le_total heur) a b

/-- Is this entry the current entry of its vertex, i.e. **not stale**? -/
def hsearch_lazy_isLive (q : Std.HashMap V ℕ) (e : LazyEntry V) : Bool := q[e.1.1]? == some e.2

omit [FinEnum V] [LawfulBEq V] in
theorem hsearch_lazy_isLive_iff (q : Std.HashMap V ℕ) (e : LazyEntry V) :
    hsearch_lazy_isLive q e = true ↔ q[e.1.1]? = some e.2 := by
  unfold hsearch_lazy_isLive
  simp

/-!
## The search state
-/

/-- A search state whose queue is a leftist heap with lazy deletion.

Apart from the queue this is the state of `SearchAlgorithms.HeuristicSearchFast`.  `queued`
maps every vertex *in the queue* to the number of its live entry; it is also the
`O(1)` test "is this neighbour still queued?".  The `Prop` fields are erased by the
compiler. -/
structure hsearch_lazy_state (V : Type) [BEq V] [Hashable V] [FinEnum V]
    (heur : V → ℕ∞) where
  /-- The visited vertices (`Finset` + hash set). -/
  vis : VisitedSet V
  /-- Path order of every *touched* vertex. -/
  orderMap : Std.HashMap V (ℕ × ℕ)
  /-- Path order of untouched vertices. -/
  orderDefault : ℕ × ℕ
  /-- Mother of every vertex whose mother has been set. -/
  motherMap : Std.HashMap V V
  /-- Fallback mother (never observed on a visited vertex). -/
  motherDefault : V
  /-- The search queue, with stale entries. -/
  heap : LHeap (LazyEntry V)
  /-- For every queued vertex, the number of its live entry. -/
  queued : Std.HashMap V ℕ
  /-- The number the next insertion will get. -/
  nextSeq : ℕ
  /-- How many nodes have been expanded (instrumentation only). -/
  expansions : ℕ
  /-- Print a progress line every `traceEvery` expansions; `0` prints nothing. -/
  traceEvery : ℕ
  /-- The heap is a heap. -/
  heap_ordered : LHeap.Ordered (hsearch_lazy_le heur) heap
  /-- Insertion numbers are pairwise distinct. -/
  seq_nodup : (heap.elems.map Prod.snd).Nodup
  /-- Every insertion number in use is below `nextSeq`. -/
  seq_lt : ∀ e ∈ heap.elems, e.2 < nextSeq
  /-- A live entry carries the current path order of its vertex. -/
  live_key : ∀ e ∈ heap.elems, hsearch_lazy_isLive queued e = true →
    e.1.2 = orderMap.getD e.1.1 orderDefault
  /-- Every queued vertex has its live entry in the heap. -/
  queued_live : ∀ (v : V) (n : ℕ), queued[v]? = some n →
    ∃ e ∈ heap.elems, e.1.1 = v ∧ e.2 = n
  /-- Only visited vertices are queued. -/
  queued_visited : ∀ v : V, queued.contains v = true → v ∈ vis.toFinset

namespace hsearch_lazy_state

variable {g : NatGraph V} {heur : V → ℕ∞}

/-- The live entries of the state, in queue order. -/
def liveEntries (s : hsearch_lazy_state V heur) : List (LazyKey V) :=
  HeapQueue.liveQueue (hsearch_lazy_key_le heur) (hsearch_lazy_isLive s.queued) s.heap

/-- **The queue represented by the state**: the vertices of the live entries, in queue order.
This is the specification of the heap; it is not evaluated during the search. -/
def queue (s : hsearch_lazy_state V heur) : List V := s.liveEntries.map Prod.fst

/-- Forgetting the heap gives the state of `SearchAlgorithms.HeuristicSearchFast`. -/
def toFastState (s : hsearch_lazy_state V heur) : hsearch_fast_state V where
  vis := s.vis
  orderMap := s.orderMap
  orderDefault := s.orderDefault
  motherMap := s.motherMap
  motherDefault := s.motherDefault
  stack := s.queue

/-- The abstract (reference) search state encoded by a lazy state. -/
@[reducible]
def toBaseState (s : hsearch_lazy_state V heur) : hsearch_search_state g where
  visited := s.vis.toFinset
  pathOrder := fun v => s.orderMap.getD v s.orderDefault
  mother := fun x => s.motherMap.getD x.1 s.motherDefault
  stack := s.queue

omit [LawfulBEq V] in
theorem toBaseState_eq_toFastState (s : hsearch_lazy_state V heur) :
    s.toBaseState (g := g) = s.toFastState.toBaseState := rfl

/-- The initial state: only `start` is visited, the queue holds `start` alone. -/
def initial (heur : V → ℕ∞) (start : V) (d : ℕ × ℕ) (traceEvery : ℕ) :
    hsearch_lazy_state V heur where
  vis := VisitedSet.singleton start
  orderMap := ∅
  orderDefault := d
  motherMap := ∅
  motherDefault := start
  heap := LHeap.node 1 ((start, d), 0) LHeap.nil LHeap.nil
  queued := (∅ : Std.HashMap V ℕ).insert start 0
  nextSeq := 1
  expansions := 0
  traceEvery := traceEvery
  heap_ordered := by simp [LHeap.Ordered]
  seq_nodup := by simp
  seq_lt := by
    intro e he
    simp only [LHeap.elems_node, LHeap.elems_nil, List.append_nil, List.mem_singleton] at he
    simp [he]
  live_key := by
    intro e he _
    simp only [LHeap.elems_node, LHeap.elems_nil, List.append_nil, List.mem_singleton] at he
    simp [he]
  queued_live := by
    intro v n hv
    rw [Std.HashMap.getElem?_insert] at hv
    split at hv
    · next h =>
      obtain rfl : start = v := eq_of_beq h
      obtain rfl : n = 0 := (Option.some.inj hv).symm
      exact ⟨((start, d), 0), by simp, rfl, rfl⟩
    · simp at hv
  queued_visited := by
    intro v hv
    rw [Std.HashMap.contains_insert] at hv
    simp only [Std.HashMap.contains_empty, Bool.or_false] at hv
    obtain rfl : start = v := eq_of_beq hv
    simp

theorem queue_initial (heur : V → ℕ∞) (start : V) (d : ℕ × ℕ) (te : ℕ) :
    (initial heur start d te).queue = [start] := by
  simp [queue, liveEntries, HeapQueue.liveQueue, HeapQueue.sortedList, initial,
    hsearch_lazy_isLive]

theorem toFastState_initial (heur : V → ℕ∞) (start : V) (d : ℕ × ℕ) (te : ℕ) :
    (initial heur start d te).toFastState = hsearch_fast_state.initial start d := by
  unfold toFastState hsearch_fast_state.initial
  rw [queue_initial]
  rfl

/-- The initial lazy state encodes the initial reference state. -/
theorem toBaseState_initial (heur : V → ℕ∞) (start : V) (d : ℕ × ℕ) (te : ℕ) :
    (initial heur start d te).toBaseState (g := g) = base_search_state_initial start d := by
  rw [toBaseState_eq_toFastState, toFastState_initial]
  exact hsearch_fast_state.toBaseState_initial start d

end hsearch_lazy_state

instance instHasBaseSearchStateLazy (g : NatGraph V) (heur : V → ℕ∞) :
    WeightedDiGraph.has_base_search_state g (ℕ × ℕ) (hsearch_lazy_state V heur) where
  to_base_state := hsearch_lazy_state.toBaseState

/-!
## The pieces of one expansion
-/

section

variable (G : NatGraphWithGenerator V) (heur : V → ℕ∞)
  (s : hsearch_lazy_state V heur) (head : V) (qt : Std.HashMap V ℕ)

/-- The abstract state without the queue, built from the *fields* of a state.  The
expansion uses this version so that it never holds a reference to the state itself while it
updates the state's hash maps — see `hsearch_lazy_itemsOf`. -/
@[reducible]
def hsearch_lazy_baseNoQueueOf (vis : VisitedSet V) (om : Std.HashMap V (ℕ × ℕ))
    (od : ℕ × ℕ) (mm : Std.HashMap V V) (md : V) :
    hsearch_search_state (G.toWeightedDiGraph) where
  visited := vis.toFinset
  pathOrder := fun v => om.getD v od
  mother := fun x => mm.getD x.1 md
  stack := []

/-- The abstract state without the queue: the per-neighbour data never looks at the queue. -/
@[reducible]
def hsearch_lazy_baseNoQueue {heur : V → ℕ∞} (s : hsearch_lazy_state V heur) :
    hsearch_search_state (G.toWeightedDiGraph) :=
  hsearch_lazy_baseNoQueueOf G s.vis s.orderMap s.orderDefault s.motherMap s.motherDefault

/-- The per-neighbour data of one expansion, as in `hsearch_fast_items` — except that the
test `v ∉ stackTail` is a lookup in `qm`, the queue map with the expanded node removed, and
that the state is given by its *fields* rather than as a whole.

Taking the fields is what makes the expansion cheap: a `Std.HashMap` is updated in place only
while it is uniquely referenced, so the expansion must not hold on to the state (which holds
a reference to each of its maps) while it updates them.  Passing the fields lets the state
die before the first update. -/
def hsearch_lazy_itemsOf (vis : VisitedSet V) (om : Std.HashMap V (ℕ × ℕ)) (od : ℕ × ℕ)
    (mm : Std.HashMap V V) (md : V) (hd : V) (qm : Std.HashMap V ℕ) :
    List (V × ((ℕ × ℕ) × V × Bool)) :=
  let g : NatGraph V := G.toWeightedDiGraph
  let ps : hsearch_search_state g := hsearch_lazy_baseNoQueueOf G vis om od mm md
  (G.neighbours hd).attach.map (fun x =>
    let v : V := x.1
    let adj : g.Adj hd v := (G.neighbours_are_adj hd v).mpr x.2
    let isVisited : Bool := vis.hashSet.contains v
    let no : ℕ × ℕ := if isVisited then new_cost ps hd v adj else path_val ps hd v adj
    let nm : V :=
      if isVisited then
        (if ps.pathOrder v = no then mm.getD v md else hd)
      else hd
    let isNew : Bool :=
      decide (heur v ≠ ⊤) &&
        (!isVisited ||
          ((!qm.contains v) &&
            decide ((ps.pathOrder v).fst > (ps.pathOrder hd).fst + g.edgeCost adj)))
    (v, no, nm, isNew))

/-- The per-neighbour data of one expansion, as in `hsearch_fast_items` — except that the
test `v ∉ stackTail` is a lookup in `qt`, the queue map with the expanded node removed. -/
def hsearch_lazy_items : List (V × ((ℕ × ℕ) × V × Bool)) :=
  hsearch_lazy_itemsOf G heur s.vis s.orderMap s.orderDefault s.motherMap s.motherDefault
    head qt

/-- The vertices entering the queue in this expansion. -/
def hsearch_lazy_newly : List V :=
  (hsearch_lazy_items G heur s head qt).filterMap (fun x => if x.2.2.2 then some x.1 else none)

/-- The entries of the vertices entering the queue. -/
def hsearch_lazy_newlyKeys : List (LazyKey V) :=
  (hsearch_lazy_items G heur s head qt).filterMap
    (fun x => if x.2.2.2 then some (x.1, x.2.1) else none)

/-- The **decrease-keys**: a neighbour that is still in the queue and whose path order this
expansion improves.  Each is recorded as its new key together with its old (now stale)
entry — the list is sorted by the latter, so that the new entries are created in queue
order. -/
def hsearch_lazy_changedPairs : List (LazyKey V × LazyEntry V) :=
  (hsearch_lazy_items G heur s head qt).filterMap (fun x =>
    match qt[x.1]? with
    | none => none
    | some n =>
      if x.2.1 == s.orderMap.getD x.1 s.orderDefault then none
      else some ((x.1, x.2.1), ((x.1, s.orderMap.getD x.1 s.orderDefault), n)))

/-- The decrease-keys, sorted by the old entry, i.e. in queue order. -/
def hsearch_lazy_changedSorted : List (LazyKey V × LazyEntry V) :=
  (hsearch_lazy_changedPairs G heur s head qt).mergeSort
    (fun a b => hsearch_lazy_le heur a.2 b.2)

/-- The keys re-inserted by the decrease-keys, in queue order. -/
def hsearch_lazy_changedKeys : List (LazyKey V) :=
  (hsearch_lazy_changedSorted G heur s head qt).map Prod.fst

/-- The vertices the expansion re-inserts. -/
def hsearch_lazy_changedV : List V :=
  (hsearch_lazy_changedKeys G heur s head qt).map Prod.fst

/-- Everything the expansion inserts into the queue: first the re-inserted nodes (in queue
order), then the newly queued ones. -/
def hsearch_lazy_pushKeys : List (LazyKey V) :=
  hsearch_lazy_changedKeys G heur s head qt ++ hsearch_lazy_newlyKeys G heur s head qt

/-- The inserted entries, numbered consecutively from `nextSeq`. -/
def hsearch_lazy_pushEntries : List (LazyEntry V) :=
  (hsearch_lazy_pushKeys G heur s head qt).zipIdx s.nextSeq

/-- The updated path-order map. -/
def hsearch_lazy_orderMap : Std.HashMap V (ℕ × ℕ) :=
  (hsearch_lazy_items G heur s head qt).foldl (fun m x => m.insert x.1 x.2.1) s.orderMap

/-- The updated mother map. -/
def hsearch_lazy_motherMap : Std.HashMap V V :=
  (hsearch_lazy_items G heur s head qt).foldl (fun m x => m.insert x.1 x.2.2.1) s.motherMap

/-- The path order after the expansion. -/
def hsearch_lazy_new_order : V → ℕ × ℕ :=
  fun v => (hsearch_lazy_orderMap G heur s head qt).getD v s.orderDefault

/-- The queue map after the expansion. -/
def hsearch_lazy_newQueued : Std.HashMap V ℕ :=
  (hsearch_lazy_pushEntries G heur s head qt).foldl (fun m e => m.insert e.1.1 e.2) qt

/-- Does the expansion replace this entry by a new one (and hence make it stale)? -/
def hsearch_lazy_isChanged (e : LazyEntry V) : Bool :=
  decide (e.1.1 ∈ hsearch_lazy_changedV G heur s head qt)

/-- The entry that replaces `e` after the expansion: same vertex, the new path order, and the
number the expansion gave it (which is the old one if the entry is not replaced). -/
def hsearch_lazy_replace (e : LazyEntry V) : LazyEntry V :=
  ((e.1.1, hsearch_lazy_new_order G heur s head qt e.1.1),
    (hsearch_lazy_newQueued G heur s head qt).getD e.1.1 0)

/-- The heap after the expansion: the root is removed and the new entries are inserted. -/
def hsearch_lazy_newHeap : LHeap (LazyEntry V) :=
  (hsearch_lazy_pushEntries G heur s head qt).foldl (LHeap.insert (hsearch_lazy_le heur))
    (LHeap.deleteMin (hsearch_lazy_le heur) s.heap)

end


end NatGraph
