import SearchAlgorithms.HeuristicSearchSorted
import SearchAlgorithms.HeapQueue
import SearchAlgorithms.SearchStepCustom

/-!
# Heuristic search with a heap as search queue

`SearchAlgorithms.HeuristicSearchSorted` keeps the search queue as a *sorted list*.  That
removes the `Θ(m log m)` re-sorting of the reference implementation, but an insertion into a
queue of length `m` still costs `O(m)` — the queue has to be copied up to the insertion
point.  Benchmarks in which the queue keeps growing (a binary tree, say) therefore still show
a cost per expansion that grows with the queue.

This module replaces the list by a **leftist heap** (`SearchAlgorithms.LeftistHeap`):

* inserting a node costs `O(log m)` and *shares* the rest of the heap — nothing is copied,
  no array is reallocated, and the cost does not depend on how many versions of the queue are
  alive;
* the next node to expand is the root of the heap, i.e. `O(1)`, and removing it is
  `O(log m)`.

The queue is never sorted during the search.  What the correctness proofs talk about — the
sorted list — is recovered *from* the heap by `HeapQueue.toQueue`, which is a specification
only: it is evaluated exactly once, when the final state is handed to the path extraction.

## Reproducing the queue of the reference implementation exactly

`List.mergeSort` is *stable*: nodes with the same `f`-value stay in the order in which they
entered the queue.  A heap does not know that order, so every entry carries a **sequence
number** and the heap is ordered by `List.zipIdxLE`, i.e. by `f`-value first and by sequence
number on ties.  The state maintains three invariants (all of them `Prop` fields, hence
erased at run time):

* `heap_ordered` — the heap is a heap for the current path order;
* `seq_nodup` — the sequence numbers are pairwise distinct, so the sorted order is *unique*
  and can be identified with the list computed by `mergeSort`;
* `seq_lt` — every sequence number is below `nextSeq`, so freshly queued nodes are ordered
  after everything already in the queue.

Together with `HeapQueue.toQueue_eq` this gives `hsearch_step_expand_heap_eq`: after every
expansion the *abstract* state is literally the one of the reference implementation, so
soundness, completeness and optimality transfer without being re-proved (see
`SearchAlgorithms.AStarHeap`).

## Decrease-key

When the expansion improves the path order of a node that is still in the queue, the heap
order may be violated (as the sorted list would be, in which case
`HeuristicSearchSorted` re-sorts).  This is detected in `O(out-degree)` by
`hsearch_heap_mustResort`, and in that — rare — case the queue is rebuilt: the entries are
read out in queue order, renumbered, and re-inserted, which costs the same `O(m log m)` as
the re-sorting of the sorted implementation.  In every other expansion the heap is only
popped once and pushed into.

## The search loop

The generic loop reads the next node off `(to_base_state s).stack`.  For a heap that list
does not exist, and building it in every iteration would defeat the purpose; the heap search
therefore runs with a step function of its own (`hsearch_heap_step`) that pops the heap, and
`WeightedDiGraph.search_exe_with_step_eq` turns the proof that the two agree
(`hsearch_heap_step_eq`) into the statement that the two searches are the same run.
-/

namespace NatGraph

open WeightedDiGraph
open SearchAlgorithms

variable {V : Type} [FinEnum V] [BEq V] [LawfulBEq V] [Hashable V]

/-!
## The comparator on decorated queue entries
-/

/-- The order in which the heap keeps the queue entries: by `f`-value, ties broken by the
sequence number.  This is the comparator with which the Lean core library states the
stability of `mergeSort`. -/
abbrev hsearch_heap_le (heur : V → ℕ∞) (o : V → ℕ × ℕ) : V × ℕ → V × ℕ → Bool :=
  List.zipIdxLE (hsearch_queue_le heur o)

omit [FinEnum V] [BEq V] [LawfulBEq V] [Hashable V] in
theorem hsearch_heap_le_trans (heur : V → ℕ∞) (o : V → ℕ × ℕ) (a b c : V × ℕ) :
    hsearch_heap_le heur o a b → hsearch_heap_le heur o b c → hsearch_heap_le heur o a c :=
  List.zipIdxLE_trans (hsearch_queue_le_trans heur o) a b c

omit [FinEnum V] [BEq V] [LawfulBEq V] [Hashable V] in
theorem hsearch_heap_le_total (heur : V → ℕ∞) (o : V → ℕ × ℕ) (a b : V × ℕ) :
    (hsearch_heap_le heur o a b || hsearch_heap_le heur o b a) = true :=
  List.zipIdxLE_total (hsearch_queue_le_total heur o) a b

omit [FinEnum V] [BEq V] [LawfulBEq V] [Hashable V] in
/-- The comparator only depends on the path order of the entries compared. -/
theorem hsearch_heap_le_congr (heur : V → ℕ∞) (o o' : V → ℕ × ℕ) (a b : V × ℕ)
    (ha : o a.1 = o' a.1) (hb : o b.1 = o' b.1) :
    hsearch_heap_le heur o a b = hsearch_heap_le heur o' a b := by
  unfold hsearch_heap_le List.zipIdxLE
  rw [hsearch_queue_le_congr heur o o' a.1 b.1 ha hb,
    hsearch_queue_le_congr heur o o' b.1 a.1 hb ha]

/-- The same comparator as `hsearch_heap_le`, but written so that the `f`-value of each
argument is computed once instead of up to four times.  Since `hsearch_heap_le` unfolds to
`List.zipIdxLE (hsearch_queue_le heur o)` and every occurrence of `add_heur _ (o _) heur`
there is shared by a `let`, the two are *definitionally* equal
(`hsearch_heap_le_fast_eq` is `rfl`), so this is purely a change of the compiled code: the
heap comparisons do two hash-map lookups instead of eight. -/
def hsearch_heap_le_fast (heur : V → ℕ∞) (o : V → ℕ × ℕ) (a b : V × ℕ) : Bool :=
  let fa := add_heur a.1 (o a.1) heur
  let fb := add_heur b.1 (o b.1) heur
  if (fa = fb || FValueComp.lt fa fb) then
    (if (fb = fa || FValueComp.lt fb fa) then decide (a.2 ≤ b.2) else true)
  else false

omit [FinEnum V] [BEq V] [LawfulBEq V] [Hashable V] in
/-- The fast comparator is the comparator. -/
theorem hsearch_heap_le_fast_eq (heur : V → ℕ∞) (o : V → ℕ × ℕ) :
    hsearch_heap_le_fast heur o = hsearch_heap_le heur o := rfl

/-!
## The search state
-/

/-- A search state whose queue is a leftist heap of `(vertex, sequence number)` pairs.

Apart from the queue this is the state of `SearchAlgorithms.HeuristicSearchFast`: hash maps
for the path order and the mother relation and a hash-set backed visited set.  `counts` holds
the multiplicity of every vertex in the queue, so that "is this neighbour still queued?" is
an `O(1)` lookup.  The four `Prop` fields are erased by the compiler. -/
structure hsearch_heap_state (V : Type) [BEq V] [Hashable V] [FinEnum V]
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
  /-- The search queue. -/
  heap : LHeap (V × ℕ)
  /-- The next sequence number to hand out. -/
  nextSeq : ℕ
  /-- Multiplicity of every vertex in the queue. -/
  counts : Std.HashMap V ℕ
  /-- The heap is a heap for the current path order. -/
  heap_ordered : LHeap.Ordered
    (hsearch_heap_le heur (fun v => orderMap.getD v orderDefault)) heap
  /-- The sequence numbers are pairwise distinct. -/
  seq_nodup : (heap.elems.map Prod.snd).Nodup
  /-- Every sequence number in use is below `nextSeq`. -/
  seq_lt : ∀ p ∈ heap.elems, p.2 < nextSeq
  /-- `counts` really are the multiplicities of the queue entries. -/
  counts_spec : ∀ v : V, counts.getD v 0 = (heap.elems.map Prod.fst).count v

namespace hsearch_heap_state

variable {g : NatGraph V} {heur : V → ℕ∞}

/-- The comparator belonging to the current path order of the state. -/
abbrev cmp (s : hsearch_heap_state V heur) : V × ℕ → V × ℕ → Bool :=
  hsearch_heap_le heur (fun v => s.orderMap.getD v s.orderDefault)

/-- **The queue represented by the state**: the entries of the heap in queue order.  This is
the specification of the heap; it is not evaluated during the search. -/
def queue (s : hsearch_heap_state V heur) : List V :=
  HeapQueue.toQueue (hsearch_queue_le heur (fun v => s.orderMap.getD v s.orderDefault)) s.heap

/-- Forgetting the heap gives the state of `SearchAlgorithms.HeuristicSearchFast`. -/
def toFastState (s : hsearch_heap_state V heur) : hsearch_fast_state V where
  vis := s.vis
  orderMap := s.orderMap
  orderDefault := s.orderDefault
  motherMap := s.motherMap
  motherDefault := s.motherDefault
  stack := s.queue

/-- The abstract (reference) search state encoded by a heap state. -/
@[reducible]
def toBaseState (s : hsearch_heap_state V heur) : hsearch_search_state g where
  visited := s.vis.toFinset
  pathOrder := fun v => s.orderMap.getD v s.orderDefault
  mother := fun x => s.motherMap.getD x.1 s.motherDefault
  stack := s.queue

omit [LawfulBEq V] in
theorem toBaseState_eq_toFastState (s : hsearch_heap_state V heur) :
    s.toBaseState (g := g) = s.toFastState.toBaseState := rfl

/-- The initial heap state: only `start` is visited, the queue holds `start` alone. -/
def initial (heur : V → ℕ∞) (start : V) (d : ℕ × ℕ) : hsearch_heap_state V heur where
  vis := VisitedSet.singleton start
  orderMap := ∅
  orderDefault := d
  motherMap := ∅
  motherDefault := start
  heap := LHeap.node 1 (start, 0) LHeap.nil LHeap.nil
  nextSeq := 1
  counts := (∅ : Std.HashMap V ℕ).insert start 1
  heap_ordered := by simp [LHeap.Ordered]
  seq_nodup := by simp
  seq_lt := by
    intro p hp
    simp only [LHeap.elems_node, LHeap.elems_nil, List.append_nil, List.mem_singleton] at hp
    simp [hp]
  counts_spec := by
    intro v
    rw [Std.HashMap.getD_insert]
    by_cases h : v = start
    · subst h; simp
    · simp [Ne.symm h]

theorem queue_initial (heur : V → ℕ∞) (start : V) (d : ℕ × ℕ) :
    (initial heur start d).queue = [start] := by
  simp [queue, HeapQueue.toQueue, HeapQueue.sortedList, initial]

theorem toFastState_initial (heur : V → ℕ∞) (start : V) (d : ℕ × ℕ) :
    (initial heur start d).toFastState = hsearch_fast_state.initial start d := by
  unfold toFastState hsearch_fast_state.initial
  rw [queue_initial]
  rfl

/-- The initial heap state encodes the initial reference state. -/
theorem toBaseState_initial (heur : V → ℕ∞) (start : V) (d : ℕ × ℕ) :
    (initial heur start d).toBaseState (g := g) = base_search_state_initial start d := by
  rw [toBaseState_eq_toFastState, toFastState_initial]
  exact hsearch_fast_state.toBaseState_initial start d

end hsearch_heap_state

instance instHasBaseSearchStateHeap (g : NatGraph V) (heur : V → ℕ∞) :
    WeightedDiGraph.has_base_search_state g (ℕ × ℕ) (hsearch_heap_state V heur) where
  to_base_state := hsearch_heap_state.toBaseState


/-!
## The pieces of one expansion step
-/

section

variable (G : NatGraphWithGenerator V) (heur : V → ℕ∞)
  (s : hsearch_heap_state V heur) (head : V)

/-- The abstract state without the queue.  The per-neighbour data below only depends on the
visited set, the path order and the mother relation, never on the queue — and *building* the
queue would mean sorting the heap, so the expansion must not construct
`hsearch_heap_state.toBaseState`. -/
@[reducible]
def hsearch_heap_baseNoQueue {heur : V → ℕ∞} (s : hsearch_heap_state V heur) :
    hsearch_search_state (G.toWeightedDiGraph) where
  visited := s.vis.toFinset
  pathOrder := fun v => s.orderMap.getD v s.orderDefault
  mother := fun x => s.motherMap.getD x.1 s.motherDefault
  stack := []

/-- Multiplicity of `v` in the queue *after* removing the expanded node. -/
def hsearch_heap_count_in_tail {heur : V → ℕ∞} (s : hsearch_heap_state V heur) (head v : V) : ℕ :=
  if v == head then s.counts.getD v 0 - 1 else s.counts.getD v 0

/-- The per-neighbour data of one expansion, as in `hsearch_fast_items` — except that the
test `v ∉ stackTail` is a multiplicity lookup instead of a scan. -/
def hsearch_heap_items : List (V × ((ℕ × ℕ) × V × Bool)) :=
  let g : NatGraph V := G.toWeightedDiGraph
  let ps : hsearch_search_state g := hsearch_heap_baseNoQueue G s
  (G.neighbours head).attach.map (fun x =>
    let v : V := x.1
    let adj : g.Adj head v := (G.neighbours_are_adj head v).mpr x.2
    let isVisited : Bool := s.vis.hashSet.contains v
    let no : ℕ × ℕ := if isVisited then new_cost ps head v adj else path_val ps head v adj
    let nm : V :=
      if isVisited then
        (if ps.pathOrder v = no then s.motherMap.getD v s.motherDefault else head)
      else head
    let isNew : Bool :=
      decide (heur v ≠ ⊤) &&
        (!isVisited ||
          (decide (hsearch_heap_count_in_tail s head v = 0) &&
            decide ((ps.pathOrder v).fst > (ps.pathOrder head).fst + g.edgeCost adj)))
    (v, no, nm, isNew))

/-- The vertices entering the queue in this expansion. -/
def hsearch_heap_newly : List V :=
  (hsearch_heap_items G heur s head).filterMap (fun x => if x.2.2.2 then some x.1 else none)

/-- The updated path-order map. -/
def hsearch_heap_orderMap : Std.HashMap V (ℕ × ℕ) :=
  (hsearch_heap_items G heur s head).foldl (fun m x => m.insert x.1 x.2.1) s.orderMap

/-- The updated mother map. -/
def hsearch_heap_motherMap : Std.HashMap V V :=
  (hsearch_heap_items G heur s head).foldl (fun m x => m.insert x.1 x.2.2.1) s.motherMap

/-- The path order after the expansion. -/
def hsearch_heap_new_order : V → ℕ × ℕ :=
  fun v => (hsearch_heap_orderMap G heur s head).getD v s.orderDefault

/-- The comparator after the expansion. -/
abbrev hsearch_heap_newCmp : V × ℕ → V × ℕ → Bool :=
  hsearch_heap_le heur (hsearch_heap_new_order G heur s head)

/-- Did the expansion change the path order of a vertex that is still in the queue?  If not,
the heap stays a heap and only has to be popped and pushed into; this is an
`O(out-degree)` test. -/
def hsearch_heap_mustResort : Bool :=
  (hsearch_heap_items G heur s head).any
    (fun x => (!(x.2.1 == s.orderMap.getD x.1 s.orderDefault))
      && decide (hsearch_heap_count_in_tail s head x.1 ≠ 0))

/-- The heap and the next sequence number after the expansion.

Normally the expanded node is popped and the new nodes are pushed, each in `O(log m)`.  Only
if a *queued* node changed its path order is the queue rebuilt: it is read out in queue
order (`hsearch_heap_qt`), renumbered and re-inserted.

`hsearch_heap_qt` is the queue entries in queue order in the rebuild case and the empty list
otherwise.  Reading the queue means sorting the heap *with the old path order*, so it has to
happen before the order map is updated: a `Std.HashMap` is modified in place only while it is
uniquely referenced, and a reference kept for this purpose would make every expansion copy
the whole map, i.e. cost `O(|touched vertices|)`. -/
def hsearch_heap_qt : List (V × ℕ) :=
  if hsearch_heap_mustResort G heur s head then
    (HeapQueue.sortedList (hsearch_queue_le heur (fun v => s.orderMap.getD v s.orderDefault))
      s.heap).tail
  else []

/-- The heap and the next sequence number after the expansion (see `hsearch_heap_qt` for the
rebuild case). -/
def hsearch_heap_pair : LHeap (V × ℕ) × ℕ :=
  if hsearch_heap_mustResort G heur s head then
    (LHeap.ofList (hsearch_heap_newCmp G heur s head)
        (((hsearch_heap_qt G heur s head).map Prod.fst
          ++ hsearch_heap_newly G heur s head).zipIdx s.nextSeq),
      s.nextSeq + (hsearch_heap_qt G heur s head).length
        + (hsearch_heap_newly G heur s head).length)
  else
    (((hsearch_heap_newly G heur s head).zipIdx s.nextSeq).foldl
        (LHeap.insert (hsearch_heap_newCmp G heur s head))
        (LHeap.deleteMin (hsearch_heap_newCmp G heur s head) s.heap),
      s.nextSeq + (hsearch_heap_newly G heur s head).length)

/-- The updated multiplicities: the expanded node leaves the queue, the new nodes enter it. -/
def hsearch_heap_counts : Std.HashMap V ℕ :=
  countsIncList (countsDec s.counts head) (hsearch_heap_newly G heur s head)

/-- The queue after the expansion, *with* the sequence numbers: this is the list the new heap
represents. -/
def hsearch_heap_D : List (V × ℕ) :=
  if hsearch_heap_mustResort G heur s head then
    (s.queue.tail ++ hsearch_heap_newly G heur s head).zipIdx s.nextSeq
  else
    (HeapQueue.sortedList (hsearch_queue_le heur (fun v => s.orderMap.getD v s.orderDefault))
      s.heap).tail ++ (hsearch_heap_newly G heur s head).zipIdx s.nextSeq

end


/-!
## The queue of the state and the expanded node
-/

section

variable (G : NatGraphWithGenerator V) (heur : V → ℕ∞)

omit [LawfulBEq V] in
/-- Multiplicities may be read off the heap: the queue is a permutation of its entries. -/
theorem hsearch_heap_queue_count (s : hsearch_heap_state V heur) (v : V) :
    s.queue.count v = (s.heap.elems.map Prod.fst).count v := by
  unfold hsearch_heap_state.queue HeapQueue.toQueue
  exact ((HeapQueue.sortedList_perm _ s.heap).map Prod.fst).count_eq v

/-- The stored multiplicity, minus the expanded node, is the multiplicity in the remaining
queue. -/
theorem hsearch_heap_count_in_tail_eq (s : hsearch_heap_state V heur) (head : V)
    (tail : List V) (hst : s.queue = head :: tail) (v : V) :
    hsearch_heap_count_in_tail s head v = tail.count v := by
  unfold hsearch_heap_count_in_tail
  rw [s.counts_spec, ← hsearch_heap_queue_count, hst, List.count_cons]
  by_cases h : v = head
  · subst h; simp
  · simp [h, Ne.symm h]

/-- The per-neighbour data is the one of `HeuristicSearchFast`: the two differ only in how
the test `v ∉ stackTail` is performed. -/
theorem hsearch_heap_items_eq (s : hsearch_heap_state V heur) (head : V) (tail : List V)
    (hst : s.queue = head :: tail) :
    hsearch_heap_items G heur s head
      = hsearch_fast_items G heur s.toFastState head tail := by
  unfold hsearch_heap_items hsearch_fast_items
  refine List.map_congr_left ?_
  rintro ⟨v, hv⟩ -
  have hc := hsearch_heap_count_in_tail_eq heur s head tail hst v
  simp only [hsearch_heap_state.toFastState, hc, List.count_eq_zero]
  rfl

/-- The path order after the expansion, as computed by `HeuristicSearchMap`. -/
theorem hsearch_heap_new_order_eq (s : hsearch_heap_state V heur) (head : V)
    (tail : List V) (hst : s.queue = head :: tail) (v : V) :
    hsearch_heap_new_order G heur s head v
      = hsearch_new_order (s.toFastState.toMapState.toBaseG G) head v := by
  unfold hsearch_heap_new_order hsearch_heap_orderMap
  rw [hsearch_heap_items_eq G heur s head tail hst,
    hsearch_fast_items_eq G heur s.toFastState head tail]
  exact hsearch_map_orderMap_getD G heur s.toFastState.toMapState head tail v

/-- If the expansion did not change the path order of any queued node, then the path order of
every node of the remaining queue is unchanged. -/
theorem hsearch_heap_new_order_eq_old (s : hsearch_heap_state V heur) (head : V)
    (tail : List V) (hst : s.queue = head :: tail)
    (hmust : hsearch_heap_mustResort G heur s head = false) (v : V) (hv : v ∈ tail) :
    hsearch_heap_new_order G heur s head v = s.orderMap.getD v s.orderDefault := by
  rw [hsearch_heap_new_order_eq G heur s head tail hst]
  by_cases hadj : (G.toWeightedDiGraph).Adj head v
  · have hvn : v ∈ G.neighbours head := (G.neighbours_are_adj head v).mp hadj
    have hkeys := hsearch_map_items_keys G heur s.toFastState.toMapState head tail
    have hmem : ∃ x ∈ hsearch_map_items G heur s.toFastState.toMapState head tail, x.1 = v := by
      have : v ∈ (hsearch_map_items G heur s.toFastState.toMapState head tail).map Prod.fst := by
        rw [hkeys]; exact hvn
      simpa using this
    obtain ⟨x, hx, hxv⟩ := hmem
    have hxo := hsearch_map_items_order G heur s.toFastState.toMapState head tail x hx
    have hxs : x ∈ hsearch_heap_items G heur s head := by
      rw [hsearch_heap_items_eq G heur s head tail hst,
        hsearch_fast_items_eq G heur s.toFastState head tail]
      exact hx
    have hall : ((!(x.2.1 == s.orderMap.getD x.1 s.orderDefault))
        && decide (hsearch_heap_count_in_tail s head x.1 ≠ 0)) = false := by
      simpa using List.any_eq_false.mp hmust x hxs
    have hct : hsearch_heap_count_in_tail s head x.1 ≠ 0 := by
      rw [hsearch_heap_count_in_tail_eq heur s head tail hst, hxv]
      exact fun h => absurd (List.count_eq_zero.mp h) (by simpa using hv)
    have hxeq : x.2.1 = s.orderMap.getD x.1 s.orderDefault := by
      rcases Bool.and_eq_false_iff.mp hall with h | h
      · simpa using h
      · exact absurd (by simpa using h) hct
    rw [← hxv, ← hxo, hxeq]
  · rw [hsearch_new_order_of_not_adj _ _ _ hadj]
    rfl

end


/-!
## The heap after one expansion represents the queue of the reference implementation
-/

section

variable (G : NatGraphWithGenerator V) (heur : V → ℕ∞) (s : hsearch_heap_state V heur)

/-- The entries of the heap in queue order (with their sequence numbers). -/
abbrev hsearch_heap_sorted : List (V × ℕ) :=
  HeapQueue.sortedList (hsearch_queue_le heur (fun v => s.orderMap.getD v s.orderDefault)) s.heap

omit [LawfulBEq V] in
theorem hsearch_heap_sorted_map_fst : (hsearch_heap_sorted heur s).map Prod.fst = s.queue := rfl

omit [LawfulBEq V] in
theorem hsearch_heap_sorted_perm : (hsearch_heap_sorted heur s).Perm s.heap.elems :=
  HeapQueue.sortedList_perm _ _

omit [LawfulBEq V] in
theorem hsearch_heap_sorted_pairwise :
    (hsearch_heap_sorted heur s).Pairwise
      (fun a b => hsearch_heap_le heur (fun v => s.orderMap.getD v s.orderDefault) a b = true) :=
  HeapQueue.sortedList_pairwise _ (hsearch_queue_le_trans heur _)
    (hsearch_queue_le_total heur _) _

omit [LawfulBEq V] in
theorem hsearch_heap_sorted_snd_nodup : ((hsearch_heap_sorted heur s).map Prod.snd).Nodup :=
  (((hsearch_heap_sorted_perm heur s).map Prod.snd).nodup_iff).mpr s.seq_nodup

omit [LawfulBEq V] in
theorem hsearch_heap_sorted_tail_mem {p : V × ℕ} (hp : p ∈ (hsearch_heap_sorted heur s).tail) :
    p ∈ s.heap.elems :=
  (hsearch_heap_sorted_perm heur s).subset (List.tail_subset _ hp)

omit [LawfulBEq V] in
/-- **The queue of the state starts with the root of the heap.**  This is what lets the
search loop read the next node off the heap. -/
theorem hsearch_heap_queue_cons (root : V × ℕ) (hp : s.heap.peek = some root) :
    s.queue = root.1 :: ((hsearch_heap_sorted heur s).tail).map Prod.fst := by
  obtain ⟨t, ht⟩ : ∃ t, hsearch_heap_sorted heur s = root :: t :=
    HeapQueue.sortedList_head _ (hsearch_queue_le_trans heur _)
      (hsearch_queue_le_total heur _) s.heap root s.heap_ordered s.seq_nodup hp
  rw [← hsearch_heap_sorted_map_fst heur s, ht]
  simp

omit [LawfulBEq V] in
/-- Removing the root of the heap leaves the tail of the queue. -/
theorem hsearch_heap_deleteMin_perm (root : V × ℕ) (hp : s.heap.peek = some root)
    (cmp' : V × ℕ → V × ℕ → Bool) :
    (LHeap.deleteMin cmp' s.heap).elems.Perm ((hsearch_heap_sorted heur s).tail) := by
  obtain ⟨t, ht⟩ : ∃ t, hsearch_heap_sorted heur s = root :: t :=
    HeapQueue.sortedList_head _ (hsearch_queue_le_trans heur _)
      (hsearch_queue_le_total heur _) s.heap root s.heap_ordered s.seq_nodup hp
  have h1 : s.heap.elems.Perm (root :: (LHeap.deleteMin cmp' s.heap).elems) :=
    LHeap.elems_deleteMin cmp' s.heap root hp
  have h2 : (root :: t).Perm s.heap.elems := by
    rw [← ht]; exact hsearch_heap_sorted_perm heur s
  have h3 : t.Perm (LHeap.deleteMin cmp' s.heap).elems :=
    (List.perm_cons root).mp (h2.trans h1)
  rw [ht]
  simpa using h3.symm

variable (head : V) (tail : List V)

omit [LawfulBEq V] in
theorem hsearch_heap_tail_map_fst (hst : s.queue = head :: tail) :
    ((hsearch_heap_sorted heur s).tail).map Prod.fst = tail := by
  rw [List.map_tail, hsearch_heap_sorted_map_fst heur s, hst, List.tail_cons]

omit [LawfulBEq V] in
/-- The vertices of the remaining queue entries are the vertices of the remaining queue. -/
theorem hsearch_heap_tail_fst_mem (hst : s.queue = head :: tail) {p : V × ℕ}
    (hp : p ∈ (hsearch_heap_sorted heur s).tail) : p.1 ∈ tail := by
  rw [← hsearch_heap_tail_map_fst heur s head tail hst]
  exact List.mem_map_of_mem hp

omit [LawfulBEq V] in
/-- In the rebuild case, `hsearch_heap_qt` is the remaining queue (with sequence numbers). -/
theorem hsearch_heap_qt_eq (hmust : hsearch_heap_mustResort G heur s head = true) :
    hsearch_heap_qt G heur s head = (hsearch_heap_sorted heur s).tail :=
  if_pos hmust

omit [LawfulBEq V] in
/-- In the rebuild case, the vertices of `hsearch_heap_qt` are the remaining queue. -/
theorem hsearch_heap_qt_map_fst (hmust : hsearch_heap_mustResort G heur s head = true) :
    (hsearch_heap_qt G heur s head).map Prod.fst = s.queue.tail := by
  rw [hsearch_heap_qt_eq G heur s head hmust, List.map_tail, hsearch_heap_sorted_map_fst]

omit [LawfulBEq V] in
/-- In the rebuild case, `hsearch_heap_qt` has the length of the remaining queue. -/
theorem hsearch_heap_qt_length (hmust : hsearch_heap_mustResort G heur s head = true) :
    (hsearch_heap_qt G heur s head).length = s.queue.tail.length := by
  rw [← hsearch_heap_qt_map_fst G heur s head hmust, List.length_map]

end

/-!
## The heap after one expansion represents the new queue

`hsearch_heap_D` is the list of queue entries (with their sequence numbers) that the new heap
holds.  The lemmas below show that it is `tail ++ newly` — the queue of the reference
implementation before sorting — with sequence numbers that are distinct and increase along
tied entries, which by `HeapQueue.toQueue_eq` means that the new heap represents exactly the
queue `(tail ++ newly).mergeSort` of the reference implementation.
-/

section

variable (G : NatGraphWithGenerator V) (heur : V → ℕ∞) (s : hsearch_heap_state V heur)

omit [LawfulBEq V] in
/-- The entries of the new heap are the queue entries of the reference implementation. -/
theorem hsearch_heap_D_map_fst (head : V) (tail : List V) (hst : s.queue = head :: tail) :
    (hsearch_heap_D G heur s head).map Prod.fst = tail ++ hsearch_heap_newly G heur s head := by
  unfold hsearch_heap_D
  split
  · rw [List.zipIdx_map_fst, hst, List.tail_cons]
  · rw [List.map_append, List.zipIdx_map_fst]
    exact congrArg (· ++ _) (hsearch_heap_tail_map_fst heur s head tail hst)

omit [LawfulBEq V] in
/-- The sequence numbers of the new queue entries are pairwise distinct. -/
theorem hsearch_heap_D_nodup (head : V) :
    ((hsearch_heap_D G heur s head).map Prod.snd).Nodup := by
  have hz : ∀ (l : List V) (n : ℕ), ((l.zipIdx n).map Prod.snd).Nodup := by
    intro l n
    exact List.pairwise_map.mpr ((SortAux.zipIdx_pairwise_snd_lt l n).imp Nat.ne_of_lt)
  unfold hsearch_heap_D
  split
  · exact hz _ _
  · rw [List.map_append]
    refine List.Nodup.append ?_ (hz _ _) ?_
    · exact List.Nodup.sublist (List.Sublist.map _ (List.tail_sublist _))
        (hsearch_heap_sorted_snd_nodup heur s)
    · intro x hx hy
      simp only [List.mem_map] at hx hy
      obtain ⟨p, hp, rfl⟩ := hx
      obtain ⟨q, hq, hq2⟩ := hy
      have h1 : p.2 < s.nextSeq := s.seq_lt p (hsearch_heap_sorted_tail_mem heur s hp)
      have h2 : s.nextSeq ≤ q.2 := (SortAux.mem_zipIdx_bounds hq).1
      omega

/-- The sequence numbers of the new queue entries increase along tied entries: entries that
are still in the queue keep their (smaller) numbers, the new ones are numbered in the order
in which they enter the queue. -/
theorem hsearch_heap_D_tie (head : V) (tail : List V) (hst : s.queue = head :: tail) :
    (hsearch_heap_D G heur s head).Pairwise (fun a b =>
      (hsearch_queue_le heur (hsearch_heap_new_order G heur s head) a.1 b.1 &&
        hsearch_queue_le heur (hsearch_heap_new_order G heur s head) b.1 a.1) = true →
      a.2 ≤ b.2) := by
  unfold hsearch_heap_D
  split
  · refine (SortAux.zipIdx_pairwise_snd_lt _ _).imp ?_
    intro a b h _
    omega
  · next hmust =>
    have hmust' : hsearch_heap_mustResort G heur s head = false := by simpa using hmust
    refine List.pairwise_append.mpr ⟨?_, ?_, ?_⟩
    · -- the entries that stay in the queue: their order did not change
      have hpw := (hsearch_heap_sorted_pairwise heur s).sublist (List.tail_sublist _)
      have htie := HeapQueue.tie_le_of_pairwise
        (hsearch_queue_le heur (fun v => s.orderMap.getD v s.orderDefault)) _ hpw
      refine htie.imp_of_mem ?_
      intro a b ha hb h hnew
      refine h ?_
      have hao := hsearch_heap_new_order_eq_old G heur s head tail hst hmust' a.1
        (hsearch_heap_tail_fst_mem heur s head tail hst ha)
      have hbo := hsearch_heap_new_order_eq_old G heur s head tail hst hmust' b.1
        (hsearch_heap_tail_fst_mem heur s head tail hst hb)
      rw [← hsearch_queue_le_congr heur (hsearch_heap_new_order G heur s head)
          (fun v => s.orderMap.getD v s.orderDefault) a.1 b.1 hao hbo,
        ← hsearch_queue_le_congr heur (hsearch_heap_new_order G heur s head)
          (fun v => s.orderMap.getD v s.orderDefault) b.1 a.1 hbo hao]
      exact hnew
    · refine (SortAux.zipIdx_pairwise_snd_lt _ _).imp ?_
      intro a b h _
      omega
    · intro a ha b hb _
      have h1 : a.2 < s.nextSeq := s.seq_lt a (hsearch_heap_sorted_tail_mem heur s ha)
      have h2 : s.nextSeq ≤ b.2 := (SortAux.mem_zipIdx_bounds hb).1
      omega

omit [LawfulBEq V] in
/-- The new heap holds exactly the new queue entries. -/
theorem hsearch_heap_pair_elems_perm (head : V) (root : V × ℕ) (hp : s.heap.peek = some root) :
    (hsearch_heap_pair G heur s head).1.elems.Perm (hsearch_heap_D G heur s head) := by
  unfold hsearch_heap_pair hsearch_heap_D
  split
  · next hmust =>
    rw [hsearch_heap_qt_map_fst G heur s head hmust]
    exact LHeap.elems_ofList _ _
  · refine (LHeap.elems_foldl_insert _ _ _).trans ?_
    exact List.Perm.append_right _ (hsearch_heap_deleteMin_perm heur s root hp _)

/-- The new heap is a heap for the new path order. -/
theorem hsearch_heap_pair_ordered (head : V) (tail : List V) (hst : s.queue = head :: tail)
    (root : V × ℕ) (hp : s.heap.peek = some root) :
    LHeap.Ordered (hsearch_heap_newCmp G heur s head) (hsearch_heap_pair G heur s head).1 := by
  unfold hsearch_heap_pair
  split
  · exact LHeap.Ordered_ofList _ (hsearch_heap_le_total heur _) (hsearch_heap_le_trans heur _) _
  · next hmust =>
    have hmust' : hsearch_heap_mustResort G heur s head = false := by simpa using hmust
    refine LHeap.Ordered_foldl_insert _ (hsearch_heap_le_total heur _)
      (hsearch_heap_le_trans heur _) _ _ ?_
    refine LHeap.Ordered_deleteMin_of_congr (hsearch_heap_le heur
        (fun v => s.orderMap.getD v s.orderDefault)) (hsearch_heap_newCmp G heur s head)
      (hsearch_heap_le_total heur _) (hsearch_heap_le_trans heur _) s.heap s.heap_ordered ?_
    intro a ha b hb
    have ha' : a ∈ (hsearch_heap_sorted heur s).tail :=
      (hsearch_heap_deleteMin_perm heur s root hp _).subset ha
    have hb' : b ∈ (hsearch_heap_sorted heur s).tail :=
      (hsearch_heap_deleteMin_perm heur s root hp _).subset hb
    exact hsearch_heap_le_congr heur _ _ a b
      (hsearch_heap_new_order_eq_old G heur s head tail hst hmust' a.1
        (hsearch_heap_tail_fst_mem heur s head tail hst ha')).symm
      (hsearch_heap_new_order_eq_old G heur s head tail hst hmust' b.1
        (hsearch_heap_tail_fst_mem heur s head tail hst hb')).symm

omit [LawfulBEq V] in
/-- All sequence numbers of the new heap are below the new `nextSeq`. -/
theorem hsearch_heap_pair_seq_lt (head : V) (root : V × ℕ) (hp : s.heap.peek = some root) :
    ∀ p ∈ (hsearch_heap_pair G heur s head).1.elems,
      p.2 < (hsearch_heap_pair G heur s head).2 := by
  intro p hpm
  have hpD := (hsearch_heap_pair_elems_perm G heur s head root hp).subset hpm
  by_cases hmust : hsearch_heap_mustResort G heur s head = true
  · simp only [hsearch_heap_D, hmust, if_true] at hpD
    simp only [hsearch_heap_pair, hmust, if_true, hsearch_heap_qt_length G heur s head hmust]
    have h2 := (SortAux.mem_zipIdx_bounds hpD).2
    rw [List.length_append] at h2
    omega
  · rw [Bool.not_eq_true] at hmust
    simp only [hsearch_heap_D, hmust, Bool.false_eq_true, if_false] at hpD
    simp only [hsearch_heap_pair, hmust, Bool.false_eq_true, if_false]
    rcases List.mem_append.mp hpD with h | h
    · have := s.seq_lt p (hsearch_heap_sorted_tail_mem heur s h)
      omega
    · exact (SortAux.mem_zipIdx_bounds h).2

/-- The multiplicities are maintained. -/
theorem hsearch_heap_pair_counts_spec (head : V) (tail : List V) (hst : s.queue = head :: tail)
    (root : V × ℕ) (hp : s.heap.peek = some root) (v : V) :
    (hsearch_heap_counts G heur s head).getD v 0
      = (((hsearch_heap_pair G heur s head).1.elems).map Prod.fst).count v := by
  rw [((hsearch_heap_pair_elems_perm G heur s head root hp).map Prod.fst).count_eq,
    hsearch_heap_D_map_fst G heur s head tail hst, List.count_append]
  unfold hsearch_heap_counts
  rw [countsIncList_getD, countsDec_getD, s.counts_spec, ← hsearch_heap_queue_count heur s v,
    hst, List.count_cons]
  by_cases h : v = head
  · subst h; simp
  · simp [h, Ne.symm h]

/-- **The new heap represents the queue of the reference implementation.** -/
theorem hsearch_heap_pair_toQueue (head : V) (tail : List V) (hst : s.queue = head :: tail)
    (root : V × ℕ) (hp : s.heap.peek = some root) :
    HeapQueue.toQueue (hsearch_queue_le heur (hsearch_heap_new_order G heur s head))
        (hsearch_heap_pair G heur s head).1
      = (tail ++ hsearch_heap_newly G heur s head).mergeSort
          (hsearch_queue_le heur (hsearch_heap_new_order G heur s head)) := by
  rw [HeapQueue.toQueue_eq _ (hsearch_queue_le_trans heur _) (hsearch_queue_le_total heur _)
      _ (hsearch_heap_D G heur s head)
      (hsearch_heap_pair_elems_perm G heur s head root hp)
      (hsearch_heap_D_nodup G heur s head)
      (hsearch_heap_D_tie G heur s head tail hst),
    hsearch_heap_D_map_fst G heur s head tail hst]

end

/-!
## The expansion step
-/

section

variable (G : NatGraphWithGenerator V) (heur : V → ℕ∞)

omit [LawfulBEq V] in
/-- The queue of the state, decomposed at the root of the heap. -/
theorem hsearch_heap_queue_cons_tail (s : hsearch_heap_state V heur) (root : V × ℕ)
    (hp : s.heap.peek = some root) : s.queue = root.1 :: s.queue.tail := by
  have h := hsearch_heap_queue_cons heur s root hp
  rw [h]
  simp

/-- **One expansion with a heap as search queue.**

The heap is popped once and pushed into once per new node; the sorted queue is never built.
Only if a node that is still in the queue changed its path order (`mustResort`) is the queue
rebuilt from the sorted list — the same fallback as in `SearchAlgorithms.HeuristicSearchSorted`.

As there, the body is spelled out with `let`s so that the per-neighbour data and the new
order map are computed exactly once and shared, and so that `mustResort` — the last read of
the *old* order map — is computed before the map is updated.  Every field is definitionally
the corresponding `hsearch_heap_*` value, which is why the four proof fields typecheck. -/
def hsearch_expand_heap_core (s : hsearch_heap_state V heur) (root : V × ℕ)
    (hp : s.heap.peek = some root) : hsearch_heap_state V heur :=
  let head : V := root.1
  let items := hsearch_heap_items G heur s head
  let newly : List V := items.filterMap (fun x => if x.2.2.2 then some x.1 else none)
  let mustResort : Bool := items.any
    (fun x => (!(x.2.1 == s.orderMap.getD x.1 s.orderDefault))
      && decide (hsearch_heap_count_in_tail s head x.1 ≠ 0))
  -- Read *every* field of the old state before any of its hash maps is updated.  After this
  -- point the only reference to `s` is the one inside the (rare) `mustResort` branch, so on
  -- the normal path the maps are uniquely referenced and are updated in place; otherwise the
  -- first `insert` copies the whole map and every expansion costs `O(|touched vertices|)`.
  let vis0 := s.vis
  let od := s.orderDefault
  let md := s.motherDefault
  let heap0 := s.heap
  let ns := s.nextSeq
  let om := s.orderMap
  let mm := s.motherMap
  let cs := s.counts
  -- the last read of the *old* order map (empty unless the queue has to be rebuilt)
  let qt : List (V × ℕ) :=
    if mustResort then
      (HeapQueue.sortedList (hsearch_queue_le heur (fun v => om.getD v od)) heap0).tail
    else []
  let newOrderMap := items.foldl (fun m x => m.insert x.1 x.2.1) om
  let newMotherMap := items.foldl (fun m x => m.insert x.1 x.2.2.1) mm
  let cmp : V × ℕ → V × ℕ → Bool :=
    hsearch_heap_le_fast heur (fun v => newOrderMap.getD v od)
  let pair : LHeap (V × ℕ) × ℕ :=
    if mustResort then
      (LHeap.ofList cmp ((qt.map Prod.fst ++ newly).zipIdx ns),
        ns + qt.length + newly.length)
    else
      ((newly.zipIdx ns).foldl (LHeap.insert cmp) (LHeap.deleteMin cmp heap0),
        ns + newly.length)
  { vis := vis0.insertList newly
    orderMap := newOrderMap
    orderDefault := od
    motherMap := newMotherMap
    motherDefault := md
    heap := pair.1
    nextSeq := pair.2
    counts := countsIncList (countsDec cs head) newly
    heap_ordered := by
      show LHeap.Ordered (hsearch_heap_newCmp G heur s root.1)
        (hsearch_heap_pair G heur s root.1).1
      exact hsearch_heap_pair_ordered G heur s root.1 s.queue.tail
        (hsearch_heap_queue_cons_tail heur s root hp) root hp
    seq_nodup := by
      show (((hsearch_heap_pair G heur s root.1).1.elems).map Prod.snd).Nodup
      exact (((hsearch_heap_pair_elems_perm G heur s root.1 root hp).map Prod.snd).nodup_iff).mpr
        (hsearch_heap_D_nodup G heur s root.1)
    seq_lt := by
      show ∀ p ∈ (hsearch_heap_pair G heur s root.1).1.elems,
        p.2 < (hsearch_heap_pair G heur s root.1).2
      exact hsearch_heap_pair_seq_lt G heur s root.1 root hp
    counts_spec := by
      show ∀ v : V, (hsearch_heap_counts G heur s root.1).getD v 0
        = (((hsearch_heap_pair G heur s root.1).1.elems).map Prod.fst).count v
      exact fun v => hsearch_heap_pair_counts_spec G heur s root.1 s.queue.tail
        (hsearch_heap_queue_cons_tail heur s root hp) root hp v }

/-- The queue after the expansion is the queue of the reference implementation. -/
theorem hsearch_expand_heap_core_queue (s : hsearch_heap_state V heur) (root : V × ℕ)
    (hp : s.heap.peek = some root) (head : V) (tail : List V) (hst : s.queue = head :: tail)
    (hhead : root.1 = head) :
    (hsearch_expand_heap_core G heur s root hp).queue
      = (tail ++ hsearch_heap_newly G heur s head).mergeSort
          (hsearch_queue_le heur (hsearch_heap_new_order G heur s head)) := by
  subst hhead
  exact hsearch_heap_pair_toQueue G heur s root.1 tail hst root hp

/-- The fields of the expansion step are the `hsearch_heap_*` values (the `let`s only make
the computation share its intermediate results). -/
theorem hsearch_expand_heap_core_toFastState (s : hsearch_heap_state V heur) (root : V × ℕ)
    (hp : s.heap.peek = some root) (head : V) (tail : List V) (hst : s.queue = head :: tail)
    (hhead : root.1 = head) :
    (hsearch_expand_heap_core G heur s root hp).toFastState
      = { vis := s.vis.insertList (hsearch_heap_newly G heur s head)
          orderMap := hsearch_heap_orderMap G heur s head
          orderDefault := s.orderDefault
          motherMap := hsearch_heap_motherMap G heur s head
          motherDefault := s.motherDefault
          stack := (tail ++ hsearch_heap_newly G heur s head).mergeSort
            (hsearch_queue_le heur (hsearch_heap_new_order G heur s head)) } := by
  rw [← hsearch_expand_heap_core_queue G heur s root hp head tail hst hhead]
  subst hhead
  rfl

/-- One expansion step of the heap search.  The node to expand is the root of the heap; the
arguments `_head` and `_tail` (which the generic search loop passes) are ignored. -/
def hsearch_step_expand_heap (s : hsearch_heap_state V heur) (_head : V) (_tail : List V) :
    hsearch_heap_state V heur :=
  match hp : s.heap.peek with
  | none => s
  | some root => hsearch_expand_heap_core G heur s root hp

/-- Whenever the heap is non-empty, the expansion step is `hsearch_expand_heap_core`. -/
theorem hsearch_step_expand_heap_eq_core (s : hsearch_heap_state V heur) (root : V × ℕ)
    (hp : s.heap.peek = some root) (head : V) (tail : List V) :
    hsearch_step_expand_heap G heur s head tail = hsearch_expand_heap_core G heur s root hp := by
  unfold hsearch_step_expand_heap
  split
  · next h => rw [h] at hp; exact absurd hp (by simp)
  · next root' h =>
    rw [h] at hp
    obtain rfl : root' = root := Option.some.inj hp
    rfl

/-- **One expansion step of the heap search produces exactly the same state as the fast
search of `SearchAlgorithms.HeuristicSearchFast`** (whenever it is applied to the queue of
its own state, which is how the search loop applies it). -/
theorem hsearch_step_expand_heap_eq_fast (s : hsearch_heap_state V heur) (head : V)
    (tail : List V) (hst : s.queue = head :: tail) :
    (hsearch_step_expand_heap G heur s head tail).toFastState
      = hsearch_step_expand_fast G heur s.toFastState head tail := by
  obtain ⟨root, hp⟩ : ∃ r, s.heap.peek = some r := by
    rcases hpk : s.heap.peek with _ | r
    · have hq : s.queue = [] := (HeapQueue.toQueue_eq_nil_iff _ s.heap).mpr hpk
      rw [hst] at hq
      exact absurd hq (by simp)
    · exact ⟨r, rfl⟩
  have hhead : root.1 = head := by
    have h := hsearch_heap_queue_cons heur s root hp
    rw [hst] at h
    exact ((List.cons.inj h).1).symm
  rw [hsearch_step_expand_heap_eq_core G heur s root hp head tail,
    hsearch_expand_heap_core_toFastState G heur s root hp head tail hst hhead]
  have hitems := hsearch_heap_items_eq G heur s head tail hst
  have hno : hsearch_heap_new_order G heur s head
      = fun v => (List.foldl (fun m x => m.insert x.1 x.2.1) s.orderMap
          (hsearch_fast_items G heur s.toFastState head tail)).getD v s.orderDefault := by
    funext v
    unfold hsearch_heap_new_order hsearch_heap_orderMap
    rw [hitems]
  unfold hsearch_step_expand_fast
  simp only [hsearch_heap_newly, hsearch_heap_orderMap, hsearch_heap_motherMap, hitems, hno]
  rfl

/-- **One expansion step of the heap search produces exactly the same abstract state as the
reference implementation `hsearch_step_expand`.** -/
theorem hsearch_step_expand_heap_eq (s : hsearch_heap_state V heur) (head : V)
    (tail : List V) (hst : s.queue = head :: tail) :
    (hsearch_step_expand_heap G heur s head tail).toBaseState (g := G.toWeightedDiGraph)
      = hsearch_step_expand (g := G.toWeightedDiGraph) heur
          (s.toBaseState (g := G.toWeightedDiGraph)) head tail := by
  rw [hsearch_heap_state.toBaseState_eq_toFastState,
    hsearch_step_expand_heap_eq_fast G heur s head tail hst,
    hsearch_heap_state.toBaseState_eq_toFastState]
  exact hsearch_step_expand_fast_eq G heur s.toFastState head tail

/-!
## The step function of the search loop
-/

/-- **The step function of the heap search.**  It reads the next node to expand off the heap
(`O(1)`) instead of off the abstract queue, which would have to be sorted first. -/
def hsearch_heap_step :
    search_step_function (G.toWeightedDiGraph) (ℕ × ℕ) (hsearch_heap_state V heur) :=
  fun goal s =>
    match hp : s.heap.peek with
    | none => (s, some false)
    | some root =>
      if root.1 = goal then (s, some true)
      else (hsearch_expand_heap_core G heur s root hp, none)

/-- **Popping the heap is the same step as taking the head of the abstract queue.**  This is
the equation that `WeightedDiGraph.search_exe_with_step_eq` needs: everything that is known
about the ordinary search loop applies to the heap search verbatim. -/
theorem hsearch_heap_step_eq :
    hsearch_heap_step G heur
      = search_stack_step (G := G.toWeightedDiGraph) (D := ℕ × ℕ)
          (state_type := hsearch_heap_state V heur) (hsearch_step_expand_heap G heur) := by
  funext goal s
  unfold hsearch_heap_step search_stack_step
  split
  · next hp =>
    have hq : (has_base_search_state.to_base_state (G := G.toWeightedDiGraph) (D := ℕ × ℕ)
        (B := hsearch_heap_state V heur) s).stack = [] :=
      (HeapQueue.toQueue_eq_nil_iff _ s.heap).mpr hp
    simp only [hq]
  · next root hp =>
    have hq : (has_base_search_state.to_base_state (G := G.toWeightedDiGraph) (D := ℕ × ℕ)
        (B := hsearch_heap_state V heur) s).stack = root.1 :: s.queue.tail :=
      hsearch_heap_queue_cons_tail heur s root hp
    simp only [hq]
    split
    · rfl
    · rw [hsearch_step_expand_heap_eq_core G heur s root hp]

end

end NatGraph
