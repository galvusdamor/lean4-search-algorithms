import SearchAlgorithms.LHeapMap
import SearchAlgorithms.AStarHeapLazyPath

/-!
# The lazy heap search with stored `f`-values (`heap_stored`)

The lazily deleted heap of `SearchAlgorithms.HeapLazyState` orders its entries by
`hsearch_lazy_key_le heur`, which computes the `f`-value `g + heur v` of **both** entries at
**every** comparison.  A heap operation makes `O(log m)` comparisons, so the heuristic is
evaluated `O(log m)` times per queue operation — and, since the per-neighbour data also asks
for it, once more per generated neighbour.  With an expensive heuristic that is where the
time goes; `SearchAlgorithms.AStarCached` hides it behind a memoising cache, but a pure cache
over a huge vertex type is itself expensive (a lazy trie of thunks, tens of kilobytes per
state).

This module removes the cause instead: a heap entry **stores its `f`-value**, computed once
when the entry is created, and the heap compares the stored values.  The heuristic of a
neighbour is wrapped in a `Thunk` and forced only when it is needed — when the neighbour
enters the queue or is re-queued — so it is evaluated at most once per queue insertion and
never for a neighbour that is already closed.

## Correctness

Nothing about the search is re-proved.  Forgetting the stored values (`erase`) maps a state of
this search onto a state of `SearchAlgorithms.HeapLazyState`; since every stored value is the
`f`-value of its entry (`KeyOk`, an invariant of the state), the two heaps perform literally
the same comparisons (`SearchAlgorithms.LHeap.map_merge` and friends), and purging, expanding
and the step function all commute with `erase` (`erase_purge`, `erase_core`,
`erase_expand`).  The generic simulation theorem of the search loop then shows that the search
returns the same path as `astar_heap_lazy_fastpath` (`astar_heap_stored_fastpath_eq_lazy`), so
soundness, completeness and optimality are inherited.
-/

namespace NatGraph

open WeightedDiGraph
open SearchAlgorithms

variable {V : Type} [FinEnum V] [BEq V] [LawfulBEq V] [Hashable V]

/-!
## Entries with a stored `f`-value
-/

/-- `add_heur` with the heuristic value given directly. -/
def addH (p : ℕ × ℕ) (h : ℕ∞) : ℕ × ℕ := ⟨p.1 + h.toNat, p.2⟩

omit [FinEnum V] [BEq V] [LawfulBEq V] [Hashable V] in
theorem add_heur_eq_addH (heur : V → ℕ∞) (v : V) (p : ℕ × ℕ) :
    add_heur v p heur = addH p (heur v) := rfl

/-- A lazy key together with its stored `f`-value. -/
abbrev StoredKey (V : Type) := LazyKey V × (ℕ × ℕ)

/-- A queue entry with a stored `f`-value. -/
abbrev StoredEntry (V : Type) := StoredKey V × ℕ

/-- The order on keys: by the **stored** `f`-value.  No heuristic is evaluated. -/
def storedKeyLe (a b : StoredKey V) : Bool := a.2 = b.2 || FValueComp.lt a.2 b.2

/-- The heap order: by stored `f`-value, ties broken by the insertion number. -/
abbrev storedLe : StoredEntry V → StoredEntry V → Bool := List.zipIdxLE storedKeyLe

/-- `storedLe` as one lexicographic comparison of natural numbers: stored `f`-value, its
tie-breaking component, then the insertion number (`storedLe_eq_fast`). -/
def storedLeFast (a b : StoredEntry V) : Bool :=
  let x := a.1.2
  let y := b.1.2
  x.1 < y.1 || (x.1 == y.1 && (x.2 < y.2 || (x.2 == y.2 && a.2 ≤ b.2)))

omit [FinEnum V] [BEq V] [LawfulBEq V] [Hashable V] in
@[csimp] theorem storedLe_eq_fast : @storedLe = @storedLeFast := by
  funext V a b
  obtain ⟨⟨k, x1, x2⟩, i⟩ := a
  obtain ⟨⟨k', y1, y2⟩, j⟩ := b
  simp only [storedLe, List.zipIdxLE, storedKeyLe, storedLeFast, FValueComp.lt,
    Nat.FValueLT]
  simp only [Prod.lex_def, Prod.mk.injEq, Bool.or_eq_true, decide_eq_true_eq]
  by_cases h1 : x1 < y1 <;> by_cases h2 : x1 = y1 <;> by_cases h3 : x2 < y2 <;>
    by_cases h4 : x2 = y2 <;> simp [h1, h2, h3, h4] <;> omega

/-- Forget the stored value of an entry. -/
abbrev eraseEntry : StoredEntry V → LazyEntry V := HeapQueue.entryMap Prod.fst

/-- The stored value of a key is its `f`-value. -/
def KeyOk (heur : V → ℕ∞) (k : StoredKey V) : Prop := k.2 = add_heur k.1.1 k.1.2 heur

omit [FinEnum V] [BEq V] [LawfulBEq V] [Hashable V] in
theorem storedKeyLe_eq (heur : V → ℕ∞) (a b : StoredKey V) (ha : KeyOk heur a)
    (hb : KeyOk heur b) : storedKeyLe a b = hsearch_lazy_key_le heur a.1 b.1 := by
  unfold storedKeyLe hsearch_lazy_key_le
  rw [ha, hb]

omit [FinEnum V] [BEq V] [LawfulBEq V] [Hashable V] in
/-- On entries whose stored values are correct, the stored order is the lazy heap order. -/
theorem storedLe_agree (heur : V → ℕ∞) (l : List (StoredEntry V))
    (hl : ∀ e ∈ l, KeyOk heur e.1) :
    LHeap.Agree storedLe (hsearch_lazy_le heur) eraseEntry l := by
  intro x hx y hy
  simp only [storedLe, hsearch_lazy_le, List.zipIdxLE, eraseEntry, HeapQueue.entryMap]
  rw [storedKeyLe_eq heur x.1 y.1 (hl x hx) (hl y hy),
    storedKeyLe_eq heur y.1 x.1 (hl y hy) (hl x hx)]
  rfl

omit [FinEnum V] [BEq V] [LawfulBEq V] [Hashable V] in
theorem storedKeyLe_agree (heur : V → ℕ∞) (l : List (StoredKey V))
    (hl : ∀ k ∈ l, KeyOk heur k) :
    ∀ a ∈ l, ∀ b ∈ l, storedKeyLe a b = hsearch_lazy_key_le heur a.1 b.1 :=
  fun a ha b hb => storedKeyLe_eq heur a b (hl a ha) (hl b hb)

/-!
## The search state
-/

/-- A state of the lazy heap search whose heap entries carry their `f`-value.  Its proof
fields are those of `hsearch_lazy_state`, stated for the heap with the stored values erased,
plus `heap_keys`: every stored value is the `f`-value of its entry. -/
structure hsearch_stored_state (V : Type) [BEq V] [Hashable V] [FinEnum V]
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
  /-- The search queue, with stale entries and stored `f`-values. -/
  heap : LHeap (StoredEntry V)
  /-- For every queued vertex, the number of its live entry. -/
  queued : Std.HashMap V ℕ
  /-- The number the next insertion will get. -/
  nextSeq : ℕ
  /-- How many nodes have been expanded (instrumentation only). -/
  expansions : ℕ
  /-- Print a progress line every `traceEvery` expansions; `0` prints nothing. -/
  traceEvery : ℕ
  /-- Every stored value is the `f`-value of its entry. -/
  heap_keys : ∀ e ∈ heap.elems, KeyOk heur e.1
  /-- The erased heap is a heap. -/
  heap_ordered : LHeap.Ordered (hsearch_lazy_le heur) (heap.map eraseEntry)
  /-- Insertion numbers are pairwise distinct. -/
  seq_nodup : ((heap.map eraseEntry).elems.map Prod.snd).Nodup
  /-- Every insertion number in use is below `nextSeq`. -/
  seq_lt : ∀ e ∈ (heap.map eraseEntry).elems, e.2 < nextSeq
  /-- A live entry carries the current path order of its vertex. -/
  live_key : ∀ e ∈ (heap.map eraseEntry).elems, hsearch_lazy_isLive queued e = true →
    e.1.2 = orderMap.getD e.1.1 orderDefault
  /-- Every queued vertex has its live entry in the heap. -/
  queued_live : ∀ (v : V) (n : ℕ), queued[v]? = some n →
    ∃ e ∈ (heap.map eraseEntry).elems, e.1.1 = v ∧ e.2 = n
  /-- Only visited vertices are queued. -/
  queued_visited : ∀ v : V, queued.contains v = true → v ∈ vis.toFinset

namespace hsearch_stored_state

variable {heur : V → ℕ∞}

/-- **Forget the stored values**: the state of the lazy heap search this state encodes.  It
is only used in proofs. -/
def erase (s : hsearch_stored_state V heur) : hsearch_lazy_state V heur where
  vis := s.vis
  orderMap := s.orderMap
  orderDefault := s.orderDefault
  motherMap := s.motherMap
  motherDefault := s.motherDefault
  heap := s.heap.map eraseEntry
  queued := s.queued
  nextSeq := s.nextSeq
  expansions := s.expansions
  traceEvery := s.traceEvery
  heap_ordered := s.heap_ordered
  seq_nodup := s.seq_nodup
  seq_lt := s.seq_lt
  live_key := s.live_key
  queued_live := s.queued_live
  queued_visited := s.queued_visited

/-- The initial state: only `start` is queued. -/
def initial (heur : V → ℕ∞) (start : V) (d : ℕ × ℕ) (traceEvery : ℕ) :
    hsearch_stored_state V heur where
  vis := VisitedSet.singleton start
  orderMap := ∅
  orderDefault := d
  motherMap := ∅
  motherDefault := start
  heap := LHeap.node 1 (((start, d), addH d (heur start)), 0) LHeap.nil LHeap.nil
  queued := (∅ : Std.HashMap V ℕ).insert start 0
  nextSeq := 1
  expansions := 0
  traceEvery := traceEvery
  heap_keys := by
    intro e he
    simp only [LHeap.elems_node, LHeap.elems_nil, List.append_nil, List.mem_singleton] at he
    subst he
    rfl
  heap_ordered := (hsearch_lazy_state.initial heur start d traceEvery).heap_ordered
  seq_nodup := (hsearch_lazy_state.initial heur start d traceEvery).seq_nodup
  seq_lt := (hsearch_lazy_state.initial heur start d traceEvery).seq_lt
  live_key := (hsearch_lazy_state.initial heur start d traceEvery).live_key
  queued_live := (hsearch_lazy_state.initial heur start d traceEvery).queued_live
  queued_visited := (hsearch_lazy_state.initial heur start d traceEvery).queued_visited

theorem erase_initial (heur : V → ℕ∞) (start : V) (d : ℕ × ℕ) (te : ℕ) :
    (initial heur start d te).erase = hsearch_lazy_state.initial heur start d te := rfl

end hsearch_stored_state

omit [LawfulBEq V] in
/-- Two lazy states with the same data are equal (the remaining fields are proofs). -/
theorem hsearch_lazy_state_ext {heur : V → ℕ∞} (s t : hsearch_lazy_state V heur)
    (h1 : s.vis = t.vis) (h2 : s.orderMap = t.orderMap) (h3 : s.orderDefault = t.orderDefault)
    (h4 : s.motherMap = t.motherMap) (h5 : s.motherDefault = t.motherDefault)
    (h6 : s.heap = t.heap) (h7 : s.queued = t.queued) (h8 : s.nextSeq = t.nextSeq)
    (h9 : s.expansions = t.expansions) (h10 : s.traceEvery = t.traceEvery) : s = t := by
  cases s
  cases t
  simp only at h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  subst h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  rfl

namespace hsearch_stored_state

variable {heur : V → ℕ∞}

/-- The queue represented by the state, computed from the **stored** `f`-values: the same
list as `s.erase.queue` (`storedQueue_eq`), but sorting it evaluates no heuristic.  The search
loop reads the base state of the final state to reconstruct the path, and a strictly evaluated
base state computes its queue — with the comparison of `hsearch_lazy_state` that would be
`O(m log m)` heuristic evaluations at the end of every search. -/
def storedQueue (s : hsearch_stored_state V heur) : List V :=
  ((HeapQueue.sortedList storedKeyLe s.heap).filter (hsearch_lazy_isLive s.queued ∘ eraseEntry)).map
    (fun e => e.1.1.1)

omit [LawfulBEq V] in
theorem storedQueue_eq (s : hsearch_stored_state V heur) : s.storedQueue = s.erase.queue := by
  unfold storedQueue hsearch_lazy_state.queue hsearch_lazy_state.liveEntries
    HeapQueue.liveQueue HeapQueue.sortedList
  simp only [erase, LHeap.elems_map]
  rw [← List.map_mergeSort (storedLe_agree heur _ s.heap_keys), List.filter_map]
  simp only [List.map_map]
  rfl

/-- The abstract state encoded by a stored state. -/
@[reducible]
def toBaseState {g : NatGraph V} (s : hsearch_stored_state V heur) : hsearch_search_state g where
  visited := s.vis.toFinset
  pathOrder := fun v => s.orderMap.getD v s.orderDefault
  mother := fun x => s.motherMap.getD x.1 s.motherDefault
  stack := s.storedQueue

omit [LawfulBEq V] in
theorem toBaseState_eq {g : NatGraph V} (s : hsearch_stored_state V heur) :
    s.toBaseState (g := g) = s.erase.toBaseState := by
  unfold toBaseState hsearch_lazy_state.toBaseState
  rw [storedQueue_eq]
  rfl

end hsearch_stored_state

/-- The base state of a stored state is the base state of the lazy state it encodes
(`hsearch_stored_state.toBaseState_eq`). -/
instance instHasBaseSearchStateStored (g : NatGraph V) (heur : V → ℕ∞) :
    WeightedDiGraph.has_base_search_state g (ℕ × ℕ) (hsearch_stored_state V heur) where
  to_base_state := hsearch_stored_state.toBaseState

omit [LawfulBEq V] in
theorem stored_to_base {g : NatGraph V} {heur : V → ℕ∞} (s : hsearch_stored_state V heur) :
    has_base_search_state.to_base_state (G := g) (D := ℕ × ℕ) s = s.erase.toBaseState :=
  s.toBaseState_eq

/-!
## Dropping the stale entries at the root
-/

section

variable (heur : V → ℕ∞)

/-- The liveness test, read off the erased entry. -/
abbrev storedIsLive (q : Std.HashMap V ℕ) : StoredEntry V → Bool :=
  hsearch_lazy_isLive q ∘ eraseEntry

omit [LawfulBEq V] in
theorem storedPurge_map (s : hsearch_stored_state V heur) :
    (HeapQueue.purge storedKeyLe (storedIsLive s.queued) s.heap).map eraseEntry
      = (hsearch_lazy_purgeState heur s.erase).heap :=
  HeapQueue.map_purge _ _ _ _ s.heap (storedLe_agree heur _ s.heap_keys)

omit [FinEnum V] [BEq V] [LawfulBEq V] [Hashable V] in
/-- Purging only drops entries. -/
theorem mem_of_mem_purge' {α : Type} (le : α → α → Bool) (p : α × ℕ → Bool) :
    ∀ (h : LHeap (α × ℕ)) (e : α × ℕ), e ∈ (HeapQueue.purge le p h).elems → e ∈ h.elems := by
  intro h
  induction h using HeapQueue.purge.induct le p with
  | case1 h hpk => intro e he; rw [HeapQueue.purge.eq_def] at he; split at he <;> simp_all
  | case2 h x hpk hx =>
    intro e he
    rw [HeapQueue.purge.eq_def] at he
    split at he
    · exact he
    · next y hy =>
      rw [hpk] at hy
      cases hy
      rw [if_pos hx] at he
      exact he
  | case3 h x hpk hx _ ih =>
    intro e he
    rw [HeapQueue.purge.eq_def] at he
    split at he
    · next hy => rw [hpk] at hy; cases hy
    · next y hy =>
      rw [hpk] at hy
      cases hy
      rw [if_neg hx] at he
      exact (LHeap.elems_deleteMin _ h x hpk).mem_iff.mpr (List.mem_cons_of_mem _ (ih e he))

/-- Drop the stale entries at the root of the heap. -/
def hsearch_stored_purgeState (s : hsearch_stored_state V heur) : hsearch_stored_state V heur where
  vis := s.vis
  orderMap := s.orderMap
  orderDefault := s.orderDefault
  motherMap := s.motherMap
  motherDefault := s.motherDefault
  heap := HeapQueue.purge storedKeyLe (storedIsLive s.queued) s.heap
  queued := s.queued
  nextSeq := s.nextSeq
  expansions := s.expansions
  traceEvery := s.traceEvery
  heap_keys := fun e he => s.heap_keys e (mem_of_mem_purge' _ _ _ e he)
  heap_ordered := by rw [storedPurge_map]; exact (hsearch_lazy_purgeState heur s.erase).heap_ordered
  seq_nodup := by rw [storedPurge_map]; exact (hsearch_lazy_purgeState heur s.erase).seq_nodup
  seq_lt := by rw [storedPurge_map]; exact (hsearch_lazy_purgeState heur s.erase).seq_lt
  live_key := by rw [storedPurge_map]; exact (hsearch_lazy_purgeState heur s.erase).live_key
  queued_live := by rw [storedPurge_map]; exact (hsearch_lazy_purgeState heur s.erase).queued_live
  queued_visited := s.queued_visited

omit [LawfulBEq V] in
/-- **Purging commutes with `erase`.** -/
theorem erase_purge (s : hsearch_stored_state V heur) :
    (hsearch_stored_purgeState heur s).erase = hsearch_lazy_purgeState heur s.erase :=
  hsearch_lazy_state_ext _ _ rfl rfl rfl rfl rfl (storedPurge_map heur s) rfl rfl rfl rfl

omit [LawfulBEq V] in
/-- After purging, the root of the heap is live. -/
theorem hsearch_stored_purge_peek_live (s : hsearch_stored_state V heur) (root : StoredEntry V)
    (hpk : (hsearch_stored_purgeState heur s).heap.peek = some root) :
    hsearch_lazy_isLive (hsearch_stored_purgeState heur s).queued (eraseEntry root) = true :=
  HeapQueue.peek_purge_live _ _ _ root hpk

end

/-!
## The pieces of one expansion
-/

section

variable (G : NatGraphWithGenerator V) (heur : V → ℕ∞)

/-- The per-neighbour data of `hsearch_lazy_itemsOf`, together with the heuristic value of the
neighbour as a **thunk**.  The test `heur v ≠ ⊤` is moved to the end of the conjunction, so the
thunk is forced only for a neighbour that would enter the queue — and a forced thunk keeps its
value, so the heuristic of a neighbour is evaluated at most once per expansion. -/
def hsearch_stored_itemsOf (vis : VisitedSet V) (om : Std.HashMap V (ℕ × ℕ)) (od : ℕ × ℕ)
    (mm : Std.HashMap V V) (md : V) (hd : V) (qm : Std.HashMap V ℕ) :
    List ((V × ((ℕ × ℕ) × V × Bool)) × Thunk ℕ∞) :=
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
    let ht : Thunk ℕ∞ := Thunk.mk (fun _ => heur v)
    let isNew : Bool :=
      (!isVisited ||
          ((!qm.contains v) &&
            decide ((ps.pathOrder v).fst > (ps.pathOrder hd).fst + g.edgeCost adj))) &&
        decide (ht.get ≠ ⊤)
    ((v, no, nm, isNew), ht))

/-- `hsearch_stored_itemsOf` with its common subterms shared: the path order of the expanded
vertex is looked up once per expansion, and the path order of a neighbour and the cost of the
edge once per neighbour (the reference version rebuilds the abstract state and repeats these
lookups inside `new_cost` and `path_val`).  It is the same function (`rfl`), installed with
`@[csimp]`. -/
def hsearch_stored_itemsOfFast (vis : VisitedSet V) (om : Std.HashMap V (ℕ × ℕ)) (od : ℕ × ℕ)
    (mm : Std.HashMap V V) (md : V) (hd : V) (qm : Std.HashMap V ℕ) :
    List ((V × ((ℕ × ℕ) × V × Bool)) × Thunk ℕ∞) :=
  let g : NatGraph V := G.toWeightedDiGraph
  let hdo : ℕ × ℕ := om.getD hd od
  (G.neighbours hd).attach.map (fun x =>
    let v : V := x.1
    let adj : g.Adj hd v := (G.neighbours_are_adj hd v).mpr x.2
    let c : ℕ := g.edgeCost adj
    let pv : ℕ × ℕ := ⟨hdo.fst + c, hdo.snd + 1⟩
    let isVisited : Bool := vis.hashSet.contains v
    let vo : ℕ × ℕ := om.getD v od
    let no : ℕ × ℕ :=
      if isVisited then
        (if vo.1 < pv.1 then vo else if vo.1 = pv.1 ∧ vo.2 < pv.2 then vo else pv)
      else pv
    let nm : V :=
      if isVisited then
        (if vo = no then mm.getD v md else hd)
      else hd
    let ht : Thunk ℕ∞ := Thunk.mk (fun _ => heur v)
    let isNew : Bool :=
      (!isVisited || ((!qm.contains v) && decide (vo.fst > hdo.fst + c))) &&
        decide (ht.get ≠ ⊤)
    ((v, no, nm, isNew), ht))

omit [LawfulBEq V] in
@[csimp] theorem hsearch_stored_itemsOf_eq_fast :
    @hsearch_stored_itemsOf = @hsearch_stored_itemsOfFast := rfl

omit [LawfulBEq V] in
theorem hsearch_stored_itemsOf_map (vis : VisitedSet V) (om : Std.HashMap V (ℕ × ℕ))
    (od : ℕ × ℕ) (mm : Std.HashMap V V) (md : V) (hd : V) (qm : Std.HashMap V ℕ) :
    (hsearch_stored_itemsOf G heur vis om od mm md hd qm).map Prod.fst
      = hsearch_lazy_itemsOf G heur vis om od mm md hd qm := by
  unfold hsearch_stored_itemsOf hsearch_lazy_itemsOf
  simp only [List.map_map]
  refine List.map_congr_left ?_
  intro x _
  simp only [Function.comp_apply, Thunk.get, Prod.mk.injEq, true_and]
  exact Bool.and_comm _ _

omit [LawfulBEq V] in
theorem hsearch_stored_itemsOf_thunk (vis : VisitedSet V) (om : Std.HashMap V (ℕ × ℕ))
    (od : ℕ × ℕ) (mm : Std.HashMap V V) (md : V) (hd : V) (qm : Std.HashMap V ℕ) :
    ∀ x ∈ hsearch_stored_itemsOf G heur vis om od mm md hd qm, x.2.get = heur x.1.1 := by
  intro x hx
  unfold hsearch_stored_itemsOf at hx
  obtain ⟨y, _, rfl⟩ := List.mem_map.mp hx
  rfl

variable (s : hsearch_stored_state V heur) (head : V) (qt : Std.HashMap V ℕ)

/-- The per-neighbour data of one expansion. -/
def hsearch_stored_items : List ((V × ((ℕ × ℕ) × V × Bool)) × Thunk ℕ∞) :=
  hsearch_stored_itemsOf G heur s.vis s.orderMap s.orderDefault s.motherMap s.motherDefault
    head qt

/-- The vertices entering the queue in this expansion. -/
def hsearch_stored_newly : List V :=
  (hsearch_stored_items G heur s head qt).filterMap
    (fun x => if x.1.2.2.2 then some x.1.1 else none)

/-- The entries of the vertices entering the queue, with their `f`-values. -/
def hsearch_stored_newlyKeys : List (StoredKey V) :=
  (hsearch_stored_items G heur s head qt).filterMap
    (fun x => if x.1.2.2.2 then some ((x.1.1, x.1.2.1), addH x.1.2.1 x.2.get) else none)

/-- The decrease-keys, with the old (now stale) entries; all `f`-values are stored. -/
def hsearch_stored_changedPairs : List (StoredKey V × StoredEntry V) :=
  (hsearch_stored_items G heur s head qt).filterMap (fun x =>
    match qt[x.1.1]? with
    | none => none
    | some n =>
      if x.1.2.1 == s.orderMap.getD x.1.1 s.orderDefault then none
      else some (((x.1.1, x.1.2.1), addH x.1.2.1 x.2.get),
        (((x.1.1, s.orderMap.getD x.1.1 s.orderDefault),
          addH (s.orderMap.getD x.1.1 s.orderDefault) x.2.get), n)))

/-- The keys re-inserted by the decrease-keys, in queue order. -/
def hsearch_stored_changedKeys : List (StoredKey V) :=
  ((hsearch_stored_changedPairs G heur s head qt).mergeSort
    (fun a b => storedLe a.2 b.2)).map Prod.fst

/-- Everything the expansion inserts into the queue, numbered from `nextSeq`. -/
def hsearch_stored_pushEntries : List (StoredEntry V) :=
  (hsearch_stored_changedKeys G heur s head qt ++ hsearch_stored_newlyKeys G heur s head qt).zipIdx
    s.nextSeq

/-- The queue map after the expansion. -/
def hsearch_stored_newQueued : Std.HashMap V ℕ :=
  (hsearch_stored_pushEntries G heur s head qt).foldl (fun m e => m.insert e.1.1.1 e.2) qt

/-- The heap after the expansion. -/
def hsearch_stored_newHeap : LHeap (StoredEntry V) :=
  (hsearch_stored_pushEntries G heur s head qt).foldl (LHeap.insert storedLe)
    (LHeap.deleteMin storedLe s.heap)

/-- The updated path-order map. -/
def hsearch_stored_orderMap : Std.HashMap V (ℕ × ℕ) :=
  (hsearch_stored_items G heur s head qt).foldl (fun m x => m.insert x.1.1 x.1.2.1) s.orderMap

/-- The updated mother map. -/
def hsearch_stored_motherMap : Std.HashMap V V :=
  (hsearch_stored_items G heur s head qt).foldl (fun m x => m.insert x.1.1 x.1.2.2.1)
    s.motherMap

/-! ### The pieces agree with those of the lazy heap search -/

omit [LawfulBEq V] in
theorem hsearch_stored_items_map :
    (hsearch_stored_items G heur s head qt).map Prod.fst
      = hsearch_lazy_items G heur s.erase head qt :=
  hsearch_stored_itemsOf_map G heur _ _ _ _ _ _ _

omit [LawfulBEq V] in
theorem hsearch_stored_items_thunk :
    ∀ x ∈ hsearch_stored_items G heur s head qt, x.2.get = heur x.1.1 :=
  hsearch_stored_itemsOf_thunk G heur _ _ _ _ _ _ _

omit [LawfulBEq V] in
theorem hsearch_stored_newly_eq :
    hsearch_stored_newly G heur s head qt = hsearch_lazy_newly G heur s.erase head qt := by
  unfold hsearch_stored_newly hsearch_lazy_newly
  rw [← hsearch_stored_items_map, List.filterMap_map]
  rfl

omit [LawfulBEq V] in
theorem hsearch_stored_newlyKeys_map :
    (hsearch_stored_newlyKeys G heur s head qt).map Prod.fst
      = hsearch_lazy_newlyKeys G heur s.erase head qt := by
  unfold hsearch_stored_newlyKeys hsearch_lazy_newlyKeys
  rw [← hsearch_stored_items_map, List.filterMap_map, List.map_filterMap]
  refine List.filterMap_congr ?_
  intro x _
  simp only [Function.comp_apply]
  split <;> rfl

omit [LawfulBEq V] in
theorem hsearch_stored_newlyKeys_ok :
    ∀ k ∈ hsearch_stored_newlyKeys G heur s head qt, KeyOk heur k := by
  intro k hk
  unfold hsearch_stored_newlyKeys at hk
  obtain ⟨x, hx, hk⟩ := List.mem_filterMap.mp hk
  split at hk
  · cases hk
    show addH x.1.2.1 x.2.get = add_heur x.1.1 x.1.2.1 heur
    rw [hsearch_stored_items_thunk G heur s head qt x hx]
    rfl
  · cases hk

omit [LawfulBEq V] in
theorem hsearch_stored_changedPairs_map :
    (hsearch_stored_changedPairs G heur s head qt).map (fun p => (p.1.1, eraseEntry p.2))
      = hsearch_lazy_changedPairs G heur s.erase head qt := by
  unfold hsearch_stored_changedPairs hsearch_lazy_changedPairs
  rw [← hsearch_stored_items_map, List.filterMap_map, List.map_filterMap]
  refine List.filterMap_congr ?_
  intro x _
  simp only [Function.comp_apply]
  split
  · next h => simp [h]
  · next n h =>
    simp only [hsearch_stored_state.erase, h]
    split <;> rfl

omit [LawfulBEq V] in
theorem hsearch_stored_changedPairs_ok :
    ∀ p ∈ hsearch_stored_changedPairs G heur s head qt, KeyOk heur p.1 ∧ KeyOk heur p.2.1 := by
  intro p hp
  unfold hsearch_stored_changedPairs at hp
  obtain ⟨x, hx, hp⟩ := List.mem_filterMap.mp hp
  have ht := hsearch_stored_items_thunk G heur s head qt x hx
  split at hp
  · cases hp
  · split at hp
    · cases hp
    · cases hp
      refine ⟨?_, ?_⟩
      · show addH x.1.2.1 x.2.get = add_heur x.1.1 x.1.2.1 heur
        rw [ht]; rfl
      · show addH (s.orderMap.getD x.1.1 s.orderDefault) x.2.get
          = add_heur x.1.1 (s.orderMap.getD x.1.1 s.orderDefault) heur
        rw [ht]; rfl

omit [LawfulBEq V] in
theorem hsearch_stored_changedKeys_map :
    (hsearch_stored_changedKeys G heur s head qt).map Prod.fst
      = hsearch_lazy_changedKeys G heur s.erase head qt := by
  unfold hsearch_stored_changedKeys hsearch_lazy_changedKeys hsearch_lazy_changedSorted
  rw [← hsearch_stored_changedPairs_map, List.map_map]
  have hag := List.map_mergeSort (r := fun a b : StoredKey V × StoredEntry V => storedLe a.2 b.2)
    (s := fun a b : LazyKey V × LazyEntry V => hsearch_lazy_le heur a.2 b.2)
    (f := fun p : StoredKey V × StoredEntry V => (p.1.1, eraseEntry p.2))
    (l := hsearch_stored_changedPairs G heur s head qt) (by
      intro a ha b hb
      exact storedLe_agree heur [a.2, b.2] (by
        intro e he
        simp only [List.mem_cons, List.not_mem_nil, or_false] at he
        rcases he with rfl | rfl
        · exact (hsearch_stored_changedPairs_ok G heur s head qt a ha).2
        · exact (hsearch_stored_changedPairs_ok G heur s head qt b hb).2)
        a.2 (by simp) b.2 (by simp))
  rw [← hag, List.map_map]
  rfl

omit [LawfulBEq V] in
theorem hsearch_stored_changedKeys_ok :
    ∀ k ∈ hsearch_stored_changedKeys G heur s head qt, KeyOk heur k := by
  intro k hk
  unfold hsearch_stored_changedKeys at hk
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hk
  exact (hsearch_stored_changedPairs_ok G heur s head qt p
    ((List.mergeSort_perm _ _).mem_iff.mp hp)).1

omit [LawfulBEq V] in
theorem hsearch_stored_pushEntries_map :
    (hsearch_stored_pushEntries G heur s head qt).map eraseEntry
      = hsearch_lazy_pushEntries G heur s.erase head qt := by
  unfold hsearch_stored_pushEntries hsearch_lazy_pushEntries hsearch_lazy_pushKeys
  rw [← hsearch_stored_changedKeys_map, ← hsearch_stored_newlyKeys_map, ← List.map_append,
    ← List.map_zipIdx]
  rfl

omit [LawfulBEq V] in
theorem hsearch_stored_pushEntries_ok :
    ∀ e ∈ hsearch_stored_pushEntries G heur s head qt, KeyOk heur e.1 := by
  intro e he
  unfold hsearch_stored_pushEntries at he
  have := List.fst_mem_of_mem_zipIdx he
  rcases List.mem_append.mp this with h | h
  · exact hsearch_stored_changedKeys_ok G heur s head qt _ h
  · exact hsearch_stored_newlyKeys_ok G heur s head qt _ h

omit [LawfulBEq V] in
theorem hsearch_stored_pushEntries_length :
    (hsearch_stored_pushEntries G heur s head qt).length
      = (hsearch_lazy_pushEntries G heur s.erase head qt).length := by
  rw [← hsearch_stored_pushEntries_map, List.length_map]

omit [LawfulBEq V] in
theorem hsearch_stored_newQueued_eq :
    hsearch_stored_newQueued G heur s head qt = hsearch_lazy_newQueued G heur s.erase head qt := by
  unfold hsearch_stored_newQueued hsearch_lazy_newQueued
  rw [← hsearch_stored_pushEntries_map, List.foldl_map]
  rfl

omit [LawfulBEq V] in
theorem hsearch_stored_newHeap_map :
    (hsearch_stored_newHeap G heur s head qt).map eraseEntry
      = hsearch_lazy_newHeap G heur s.erase head qt := by
  unfold hsearch_stored_newHeap hsearch_lazy_newHeap
  have hok : ∀ e ∈ (LHeap.deleteMin storedLe s.heap).elems
      ++ hsearch_stored_pushEntries G heur s head qt, KeyOk heur e.1 := by
    intro e he
    rcases List.mem_append.mp he with h | h
    · cases hh : s.heap with
      | nil => rw [hh] at h; simp [LHeap.deleteMin] at h
      | node k x l r =>
        rw [hh] at h
        have := (LHeap.elems_deleteMin storedLe (LHeap.node k x l r) x rfl).mem_iff.mpr
          (List.mem_cons_of_mem _ h)
        rw [← hh] at this
        exact s.heap_keys e this
    · exact hsearch_stored_pushEntries_ok G heur s head qt e h
  rw [LHeap.map_foldl_insert _ _ _ _ _ (storedLe_agree heur _ hok),
    LHeap.map_deleteMin _ _ _ _ (storedLe_agree heur _ s.heap_keys),
    hsearch_stored_pushEntries_map]
  rfl

omit [LawfulBEq V] in
theorem hsearch_stored_newHeap_ok :
    ∀ e ∈ (hsearch_stored_newHeap G heur s head qt).elems, KeyOk heur e.1 := by
  intro e he
  unfold hsearch_stored_newHeap at he
  rcases List.mem_append.mp ((LHeap.elems_foldl_insert _ _ _).mem_iff.mp he) with h | h
  · cases hh : s.heap with
    | nil => rw [hh] at h; simp [LHeap.deleteMin] at h
    | node k x l r =>
      rw [hh] at h
      have := (LHeap.elems_deleteMin storedLe (LHeap.node k x l r) x rfl).mem_iff.mpr
        (List.mem_cons_of_mem _ h)
      rw [← hh] at this
      exact s.heap_keys e this
  · exact hsearch_stored_pushEntries_ok G heur s head qt e h

omit [LawfulBEq V] in
theorem hsearch_stored_orderMap_eq :
    hsearch_stored_orderMap G heur s head qt = hsearch_lazy_orderMap G heur s.erase head qt := by
  unfold hsearch_stored_orderMap hsearch_lazy_orderMap
  rw [← hsearch_stored_items_map, List.foldl_map]
  rfl

omit [LawfulBEq V] in
theorem hsearch_stored_motherMap_eq :
    hsearch_stored_motherMap G heur s head qt = hsearch_lazy_motherMap G heur s.erase head qt := by
  unfold hsearch_stored_motherMap hsearch_lazy_motherMap
  rw [← hsearch_stored_items_map, List.foldl_map]
  rfl

end

/-!
## One expansion
-/

section

variable (G : NatGraphWithGenerator V) (heur : V → ℕ∞)

omit [LawfulBEq V] in
theorem stored_peek_erase (s : hsearch_stored_state V heur) (root : StoredEntry V)
    (hp : s.heap.peek = some root) : s.erase.heap.peek = some (eraseEntry root) := by
  show (s.heap.map eraseEntry).peek = _
  rw [LHeap.peek_map, hp]
  rfl

/-- The lazy expansion that `hsearch_stored_core` simulates. -/
abbrev hsearch_stored_core_ref (s : hsearch_stored_state V heur) (root : StoredEntry V)
    (hp : s.heap.peek = some root)
    (hlive : hsearch_lazy_isLive s.queued (eraseEntry root) = true) :
    hsearch_lazy_state V heur :=
  hsearch_expand_lazy_core G heur s.erase (eraseEntry root) (stored_peek_erase heur s root hp) hlive

/-- **One expansion of the search with stored `f`-values.**  It is `hsearch_expand_lazy_core`
with the `f`-value of every new entry computed once, from the thunk of the neighbour, and the
heap ordered by the stored values.  As there, every field of the old state is read before any
of its hash maps is updated, so that the maps are updated in place. -/
def hsearch_stored_core (s : hsearch_stored_state V heur) (root : StoredEntry V)
    (hp : s.heap.peek = some root)
    (hlive : hsearch_lazy_isLive s.queued (eraseEntry root) = true) :
    hsearch_stored_state V heur :=
  let head : V := root.1.1.1
  let vis0 := s.vis
  let om := s.orderMap
  let od := s.orderDefault
  let mm := s.motherMap
  let md := s.motherDefault
  let heap0 := s.heap
  let q0 := s.queued
  let ns := s.nextSeq
  let ex := s.expansions
  let te := s.traceEvery
  let qt : Std.HashMap V ℕ := q0.erase head
  let items := hsearch_stored_itemsOf G heur vis0 om od mm md head qt
  let newly : List V := items.filterMap (fun x => if x.1.2.2.2 then some x.1.1 else none)
  let newlyKeys : List (StoredKey V) := items.filterMap
    (fun x => if x.1.2.2.2 then some ((x.1.1, x.1.2.1), addH x.1.2.1 x.2.get) else none)
  let changedPairs : List (StoredKey V × StoredEntry V) := items.filterMap (fun x =>
    match qt[x.1.1]? with
    | none => none
    | some n =>
      let ov := om.getD x.1.1 od
      if x.1.2.1 == ov then none
      else
        let hv := x.2.get
        some (((x.1.1, x.1.2.1), addH x.1.2.1 hv), (((x.1.1, ov), addH ov hv), n)))
  let changedKeys : List (StoredKey V) :=
    (changedPairs.mergeSort (fun a b => storedLe a.2 b.2)).map Prod.fst
  let pushEntries : List (StoredEntry V) := (changedKeys ++ newlyKeys).zipIdx ns
  let newQueued : Std.HashMap V ℕ := pushEntries.foldl (fun m e => m.insert e.1.1.1 e.2) qt
  let newHeap : LHeap (StoredEntry V) :=
    pushEntries.foldl (LHeap.insert storedLe) (LHeap.deleteMin storedLe heap0)
  let newOrderMap := items.foldl (fun m x => m.insert x.1.1 x.1.2.1) om
  let newMotherMap := items.foldl (fun m x => m.insert x.1.1 x.1.2.2.1) mm
  let newVis := vis0.insertList newly
  traceIf (te != 0 && (ex + 1) % te == 0)
    (fun _ => s!"[search] expanded {ex + 1} nodes | queue {newQueued.size} | visited {newVis.hashSet.size} | insertions {ns + pushEntries.length}")
  { vis := newVis
    orderMap := newOrderMap
    orderDefault := od
    motherMap := newMotherMap
    motherDefault := md
    heap := newHeap
    queued := newQueued
    nextSeq := ns + pushEntries.length
    expansions := ex + 1
    traceEvery := te
    heap_keys := hsearch_stored_newHeap_ok G heur s root.1.1.1 (s.queued.erase root.1.1.1)
    heap_ordered := by
      show LHeap.Ordered _ ((hsearch_stored_newHeap G heur s root.1.1.1
        (s.queued.erase root.1.1.1)).map eraseEntry)
      rw [hsearch_stored_newHeap_map]
      exact hsearch_lazy_newHeap_ordered G heur s.erase root.1.1.1 (s.queued.erase root.1.1.1)
    seq_nodup := by
      show (((hsearch_stored_newHeap G heur s root.1.1.1
        (s.queued.erase root.1.1.1)).map eraseEntry).elems.map Prod.snd).Nodup
      rw [hsearch_stored_newHeap_map]
      have hp' := stored_peek_erase heur s root hp
      obtain ⟨T, hT⟩ := hsearch_lazy_sorted_eq_cons heur s.erase (eraseEntry root) hp'
      exact hsearch_lazy_newHeap_nodup G heur s.erase (eraseEntry root) T hp' hT
        (s.queued.erase root.1.1.1)
    seq_lt := by
      show ∀ e ∈ ((hsearch_stored_newHeap G heur s root.1.1.1
        (s.queued.erase root.1.1.1)).map eraseEntry).elems,
          e.2 < s.nextSeq + (hsearch_stored_pushEntries G heur s root.1.1.1
            (s.queued.erase root.1.1.1)).length
      rw [hsearch_stored_newHeap_map, hsearch_stored_pushEntries_length]
      have hp' := stored_peek_erase heur s root hp
      obtain ⟨T, hT⟩ := hsearch_lazy_sorted_eq_cons heur s.erase (eraseEntry root) hp'
      exact hsearch_lazy_newHeap_seq_lt G heur s.erase (eraseEntry root) T hp' hT
        (s.queued.erase root.1.1.1)
    live_key := by
      show ∀ e ∈ ((hsearch_stored_newHeap G heur s root.1.1.1
        (s.queued.erase root.1.1.1)).map eraseEntry).elems,
          hsearch_lazy_isLive (hsearch_stored_newQueued G heur s root.1.1.1
            (s.queued.erase root.1.1.1)) e = true →
          e.1.2 = (hsearch_stored_orderMap G heur s root.1.1.1
            (s.queued.erase root.1.1.1)).getD e.1.1 s.orderDefault
      rw [hsearch_stored_newHeap_map, hsearch_stored_newQueued_eq, hsearch_stored_orderMap_eq]
      have hp' := stored_peek_erase heur s root hp
      obtain ⟨T, hT⟩ := hsearch_lazy_sorted_eq_cons heur s.erase (eraseEntry root) hp'
      exact hsearch_lazy_newHeap_live_key G heur s.erase (eraseEntry root) T hp' hlive hT
    queued_live := by
      show ∀ (v : V) (n : ℕ), (hsearch_stored_newQueued G heur s root.1.1.1
          (s.queued.erase root.1.1.1))[v]? = some n →
        ∃ e ∈ ((hsearch_stored_newHeap G heur s root.1.1.1
          (s.queued.erase root.1.1.1)).map eraseEntry).elems, e.1.1 = v ∧ e.2 = n
      rw [hsearch_stored_newHeap_map, hsearch_stored_newQueued_eq]
      have hp' := stored_peek_erase heur s root hp
      obtain ⟨T, hT⟩ := hsearch_lazy_sorted_eq_cons heur s.erase (eraseEntry root) hp'
      exact hsearch_lazy_newHeap_queued_live G heur s.erase (eraseEntry root) T hp' hlive hT
    queued_visited := by
      show ∀ v : V, (hsearch_stored_newQueued G heur s root.1.1.1
          (s.queued.erase root.1.1.1)).contains v = true →
        v ∈ (s.vis.insertList (hsearch_stored_newly G heur s root.1.1.1
          (s.queued.erase root.1.1.1))).toFinset
      rw [hsearch_stored_newQueued_eq, hsearch_stored_newly_eq]
      exact hsearch_lazy_newQueued_visited G heur s.erase (eraseEntry root) }

/-- **One expansion commutes with `erase`.** -/
theorem erase_core (s : hsearch_stored_state V heur) (root : StoredEntry V)
    (hp : s.heap.peek = some root)
    (hlive : hsearch_lazy_isLive s.queued (eraseEntry root) = true) :
    (hsearch_stored_core G heur s root hp hlive).erase
      = hsearch_stored_core_ref G heur s root hp hlive := by
  unfold hsearch_stored_core hsearch_stored_core_ref hsearch_expand_lazy_core
  simp only [traceIf_eq]
  refine hsearch_lazy_state_ext _ _ ?_ ?_ rfl ?_ rfl ?_ ?_ ?_ rfl rfl
  · show s.vis.insertList (hsearch_stored_newly G heur s root.1.1.1 (s.queued.erase root.1.1.1))
      = s.erase.vis.insertList (hsearch_lazy_newly G heur s.erase root.1.1.1
          (s.queued.erase root.1.1.1))
    rw [hsearch_stored_newly_eq]
    rfl
  · exact hsearch_stored_orderMap_eq G heur s _ _
  · exact hsearch_stored_motherMap_eq G heur s _ _
  · exact hsearch_stored_newHeap_map G heur s _ _
  · exact hsearch_stored_newQueued_eq G heur s _ _
  · show s.nextSeq + (hsearch_stored_pushEntries G heur s root.1.1.1
        (s.queued.erase root.1.1.1)).length
      = s.erase.nextSeq + (hsearch_lazy_pushEntries G heur s.erase root.1.1.1
        (s.queued.erase root.1.1.1)).length
    rw [hsearch_stored_pushEntries_length]
    rfl

/-- The lazy expansion only depends on the state, not on the proofs of the root. -/
theorem hsearch_expand_lazy_core_congr (s t : hsearch_lazy_state V heur) (hst : s = t)
    (root : LazyEntry V) (hp : s.heap.peek = some root) (hp' : t.heap.peek = some root)
    (hl : hsearch_lazy_isLive s.queued root = true)
    (hl' : hsearch_lazy_isLive t.queued root = true) :
    hsearch_expand_lazy_core G heur s root hp hl = hsearch_expand_lazy_core G heur t root hp' hl' := by
  subst hst
  rfl

/-- One expansion step: purge the stale entries at the root, then expand the root. -/
def hsearch_step_expand_stored (s : hsearch_stored_state V heur) (_head : V) (_tail : List V) :
    hsearch_stored_state V heur :=
  match hpk : (hsearch_stored_purgeState heur s).heap.peek with
  | none => hsearch_stored_purgeState heur s
  | some root => hsearch_stored_core G heur (hsearch_stored_purgeState heur s) root hpk
      (hsearch_stored_purge_peek_live heur s root hpk)

omit [LawfulBEq V] in
theorem stored_purge_peek (s : hsearch_stored_state V heur) :
    (hsearch_lazy_purgeState heur s.erase).heap.peek
      = ((hsearch_stored_purgeState heur s).heap.peek).map eraseEntry := by
  rw [← erase_purge]
  exact LHeap.peek_map _ _

/-- **An expansion step commutes with `erase`.** -/
theorem erase_expand (s : hsearch_stored_state V heur) (head : V) (tail : List V) :
    (hsearch_step_expand_stored G heur s head tail).erase
      = hsearch_step_expand_lazy G heur s.erase head tail := by
  unfold hsearch_step_expand_stored
  split
  · next hpk =>
    have hpk' : (hsearch_lazy_purgeState heur s.erase).heap.peek = none := by
      rw [stored_purge_peek, hpk]; rfl
    unfold hsearch_step_expand_lazy hsearch_expand_lazy_purged
    split
    · rw [erase_purge]
    · next r hr => rw [hpk'] at hr; cases hr
  · next root hpk =>
    have hpk' : (hsearch_lazy_purgeState heur s.erase).heap.peek = some (eraseEntry root) := by
      rw [stored_purge_peek, hpk]; rfl
    rw [hsearch_step_expand_lazy_eq_core G heur s.erase (eraseEntry root) hpk' head tail,
      erase_core]
    exact hsearch_expand_lazy_core_congr G heur _ _ (erase_purge heur s) _ _ _ _ _

/-!
## The step function of the search loop
-/

/-- **The step function of the search with stored `f`-values**: the next node to expand is
read off the heap. -/
def hsearch_stored_step :
    search_step_function (G.toWeightedDiGraph) (ℕ × ℕ) (hsearch_stored_state V heur) :=
  fun goal s =>
    match hpk : (hsearch_stored_purgeState heur s).heap.peek with
    | none => (s, some false)
    | some root =>
      if root.1.1.1 = goal then (s, some true)
      else
        (hsearch_stored_core G heur (hsearch_stored_purgeState heur s) root hpk
          (hsearch_stored_purge_peek_live heur s root hpk), none)

omit [LawfulBEq V] in
/-- If the purged heap is empty, the queue is empty. -/
theorem stored_queue_nil (s : hsearch_stored_state V heur)
    (hpk : (hsearch_stored_purgeState heur s).heap.peek = none) : s.erase.queue = [] := by
  rw [← hsearch_lazy_purgeState_queue heur s.erase]
  refine hsearch_lazy_queue_eq_nil_of_peek_none heur _ ?_
  rw [stored_purge_peek, hpk]
  rfl

omit [LawfulBEq V] in
/-- If the purged heap has a root, the queue starts with its vertex. -/
theorem stored_queue_cons (s : hsearch_stored_state V heur) (root : StoredEntry V)
    (hpk : (hsearch_stored_purgeState heur s).heap.peek = some root) :
    s.erase.queue = root.1.1.1 :: s.erase.queue.tail := by
  have hpk' : (hsearch_lazy_purgeState heur s.erase).heap.peek = some (eraseEntry root) := by
    rw [stored_purge_peek, hpk]
    rfl
  obtain ⟨T, hT⟩ := hsearch_lazy_sorted_eq_cons heur (hsearch_lazy_purgeState heur s.erase)
    (eraseEntry root) hpk'
  have h := hsearch_lazy_queue_cons heur (hsearch_lazy_purgeState heur s.erase) (eraseEntry root)
    T (hsearch_lazy_purge_peek_live heur s.erase (eraseEntry root) hpk') hT
  rw [hsearch_lazy_purgeState_queue] at h
  rw [h]
  rfl

/-- Popping the heap is the same step as taking the head of the abstract queue. -/
theorem hsearch_stored_step_eq :
    hsearch_stored_step G heur
      = search_stack_step (G := G.toWeightedDiGraph) (D := ℕ × ℕ)
          (state_type := hsearch_stored_state V heur) (hsearch_step_expand_stored G heur) := by
  funext goal s
  unfold hsearch_stored_step search_stack_step
  show _ = (match s.storedQueue with
    | [] => (s, some false)
    | h :: t => if h = goal then (s, some true) else (hsearch_step_expand_stored G heur s h t, none))
  rw [hsearch_stored_state.storedQueue_eq]
  split
  · next hpk => rw [stored_queue_nil heur s hpk]
  · next root hpk =>
    rw [stored_queue_cons heur s root hpk]
    simp only
    split
    · rfl
    · unfold hsearch_step_expand_stored
      split
      · next h => rw [hpk] at h; cases h
      · next r h =>
        rw [hpk] at h
        cases h
        rfl

/-!
## The search
-/

/-- The termination metric: that of the lazy state the state encodes. -/
def hsearch_stored_termination_metric (s : hsearch_stored_state V heur) : ℕ × ℕ × ℕ × ℕ :=
  hsearch_lazy_termination_metric G heur s.erase

theorem hsearch_stored_expand_metric_reduction (goal : V) :
    WeightedDiGraph.termination_proof_for_expand (G := G.toWeightedDiGraph) (D := ℕ × ℕ)
      (state_type := hsearch_stored_state V heur) (hsearch_step_expand_stored G heur) goal
      (hsearch_stored_termination_metric G heur) := by
  intro state head tail h
  have := hsearch_lazy_expand_metric_reduction G heur goal state.erase head tail
    ⟨h.1, by
      show state.erase.queue = head :: tail
      rw [← hsearch_stored_state.storedQueue_eq]
      exact h.2⟩
  unfold hsearch_stored_termination_metric
  rw [erase_expand]
  exact this

theorem hsearch_stored_expand_keeps_base_invars (start goal : V) :
    WeightedDiGraph.base_invar_carries_over_expand (G := G.toWeightedDiGraph) (D := ℕ × ℕ)
      (state_type := hsearch_stored_state V heur) (hsearch_step_expand_stored G heur) goal
      (WeightedDiGraph.search_invar_all_basic (G := G.toWeightedDiGraph) (D := ℕ × ℕ)
        (hsearch_expandable heur) start) := by
  intro s head tail h
  rw [stored_to_base] at h
  have := hsearch_lazy_expand_keeps_base_invars G heur start goal s.erase head tail h
  rw [stored_to_base, erase_expand]
  exact this

theorem hsearch_stored_toBaseState_initial (start : V) (d : ℕ × ℕ) (te : ℕ) :
    has_base_search_state.to_base_state (G := G.toWeightedDiGraph) (D := ℕ × ℕ)
      (hsearch_stored_state.initial heur start d te) = base_search_state_initial start d := by
  rw [stored_to_base, hsearch_stored_state.erase_initial]
  exact hsearch_lazy_state.toBaseState_initial heur start d te

/-- **A\* with a lazily deleted heap whose entries store their `f`-value**, with linear-time
path reconstruction.  The heuristic is evaluated at most once per queue insertion and never by
a comparison.  `te` is the trace interval (`0` prints nothing). -/
def astar_heap_stored_fastpath (start : V) (goal : V) (te : ℕ := 100) :
    Option ((G.toWeightedDiGraph).Path start goal) :=
  WeightedDiGraph.search_exe_with_step_eq_fast (G := G.toWeightedDiGraph) (start := start)
    (start_state := hsearch_stored_state.initial heur start ⟨0, 0⟩ te)
    (termination_metric := hsearch_stored_termination_metric G heur)
    (hsearch_step_expand_stored G heur) goal
    (hsearch_stored_step G heur) (hsearch_stored_step_eq G heur)
    (hsearch_stored_expand_metric_reduction G heur goal)
    (hsearch_stored_expand_keeps_base_invars G heur start goal)
    (hsearch_stored_toBaseState_initial G heur start (0, 0) te)

/-- **The search with stored `f`-values returns the same path as `astar_heap_lazy_fastpath`.** -/
theorem astar_heap_stored_fastpath_eq_lazy (start : V) (goal : V) (te : ℕ) :
    astar_heap_stored_fastpath G heur start goal te
      = astar_heap_lazy_fastpath G heur start goal te := by
  rw [astar_heap_lazy_fastpath_eq_lazy, astar_heap_lazy_eq_stack]
  unfold astar_heap_stored_fastpath
  rw [WeightedDiGraph.search_exe_with_step_eq_fast_eq,
    WeightedDiGraph.search_exe_with_step_eq_stack]
  exact (search_exe_with_stack_step_sim_of_stack' (G := G.toWeightedDiGraph) (D := ℕ × ℕ)
    (A := hsearch_stored_state V heur) (B := hsearch_lazy_state V heur)
    (fun s => s.erase) (fun a => (stored_to_base a).symm)
    (hsearch_step_expand_stored G heur) (hsearch_step_expand_lazy G heur)
    (fun s head tail _ => erase_expand G heur s head tail)
    (hsearch_stored_state.erase_initial heur start (0, 0) te)
    (hsearch_stored_termination_metric G heur) (hsearch_lazy_termination_metric G heur)
    (hsearch_stored_expand_metric_reduction G heur goal)
    (hsearch_stored_expand_keeps_base_invars G heur start goal)
    (hsearch_stored_toBaseState_initial G heur start (0, 0) te)
    (hsearch_lazy_expand_metric_reduction G heur goal)
    (hsearch_lazy_expand_keeps_base_invars G heur start goal)
    (hsearch_lazy_state.toBaseState_initial heur start (0, 0) te)).symm

/-- **The search with stored `f`-values computes the same result as `astar`.** -/
theorem astar_heap_stored_fastpath_eq (start : V) (goal : V) (te : ℕ) :
    astar_heap_stored_fastpath G heur start goal te
      = astar (g := G.toWeightedDiGraph) heur start goal := by
  rw [astar_heap_stored_fastpath_eq_lazy, astar_heap_lazy_fastpath_eq]

/-! ### Multi-goal search -/

/-- Multi-goal A* with stored `f`-values and linear-time path reconstruction. -/
def astar_multigoal_heap_stored_fastpath (start : V)
    (is_goal : V → Prop) [DecidablePred is_goal] (te : ℕ := 100) :
    Option ((thegoal : {v : V // is_goal v}) × (G.toWeightedDiGraph).Path start thegoal) :=
  astar_multigoal_postprocess (g := G.toWeightedDiGraph) start is_goal
    (astar_heap_stored_fastpath (add_artificial_goal_gen G is_goal) (opt_heur heur) (some start)
      none te)

/-- The multi-goal search with stored `f`-values returns the same result as
`astar_multigoal_heap_lazy_fastpath`. -/
theorem astar_multigoal_heap_stored_fastpath_eq_lazy (start : V)
    (is_goal : V → Prop) [DecidablePred is_goal] (te : ℕ) :
    astar_multigoal_heap_stored_fastpath G heur start is_goal te
      = astar_multigoal_heap_lazy_fastpath G heur start is_goal te := by
  unfold astar_multigoal_heap_stored_fastpath astar_multigoal_heap_lazy_fastpath
  rw [astar_heap_stored_fastpath_eq_lazy]

end

end NatGraph
