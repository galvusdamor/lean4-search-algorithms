import SearchAlgorithms.HeapLazyState

/-!
# The expansion step of the lazily deleted heap search

`SearchAlgorithms.HeapLazyState` defines the state of the `heap_lazy` search and the pieces of
one expansion.  This module proves that one expansion produces exactly the abstract state of
the reference implementation, and defines the search step that pops the heap.

The chain of the argument is:

* `hsearch_lazy_queue_eq` — the queue of a state is the stable sort of its live entries (the
  core lemma on staleness, `HeapQueue.liveQueue_eq`, transported to vertices);
* `hsearch_lazy_queue_cons`, `hsearch_lazy_qtail_contains_iff` — the queue decomposed at the
  root, and the `O(1)` test "is this neighbour still queued?";
* `hsearch_lazy_items_eq` — the per-neighbour data is the one of `HeuristicSearchFast`;
* `hsearch_lazy_D_ref_*` — the live entries after the expansion, listed in the order in which
  the reference implementation feeds them to `mergeSort`, and the proof that their numbers
  break ties the way the stable sort does;
* `hsearch_expand_lazy_core_queue` — hence the queue after the expansion is literally
  `(tail ++ newly).mergeSort`, the queue of the reference implementation;
* `hsearch_step_expand_lazy_eq` — hence the abstract state after the expansion is the
  reference state.
-/

namespace NatGraph

open WeightedDiGraph
open SearchAlgorithms

variable {V : Type} [FinEnum V] [BEq V] [LawfulBEq V] [Hashable V]

/-!
## From the live entries to the reference queue
-/

section

variable (heur : V → ℕ∞)

omit [LawfulBEq V] in
/-- **The queue of a state is the stable sort of its live entries**: the core lemma on
staleness (`HeapQueue.liveQueue_eq`), transported to vertices.  `d` is any list of the heap's
entries; only the live ones matter, and of those only that their numbers increase along tied
entries. -/
theorem hsearch_lazy_queue_eq (s : hsearch_lazy_state V heur) (d : List (LazyEntry V))
    (hperm : s.heap.elems.Perm d)
    (htie : (d.filter (hsearch_lazy_isLive s.queued)).Pairwise
      (fun a b => (hsearch_lazy_key_le heur a.1 b.1 && hsearch_lazy_key_le heur b.1 a.1) = true →
        a.2 ≤ b.2)) :
    s.queue = ((d.filter (hsearch_lazy_isLive s.queued)).map (fun e => e.1.1)).mergeSort
      (hsearch_queue_le heur (fun v => s.orderMap.getD v s.orderDefault)) := by
  have hnd : (d.map Prod.snd).Nodup := ((hperm.map Prod.snd).nodup_iff).mp s.seq_nodup
  have h1 := HeapQueue.liveQueue_eq (hsearch_lazy_key_le heur) (hsearch_lazy_key_le_trans heur)
    (hsearch_lazy_key_le_total heur) (hsearch_lazy_isLive s.queued) s.heap d hperm hnd htie
  have hkey : ∀ a ∈ (d.filter (hsearch_lazy_isLive s.queued)).map Prod.fst,
      a.2 = s.orderMap.getD a.1 s.orderDefault := by
    intro a ha
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp ha
    have hlive : hsearch_lazy_isLive s.queued e = true := (List.mem_filter.mp he).2
    exact s.live_key e (hperm.mem_iff.mpr (List.mem_of_mem_filter he)) hlive
  show (HeapQueue.liveQueue _ _ _).map Prod.fst = _
  rw [h1, show ((d.filter (hsearch_lazy_isLive s.queued)).map (fun e => e.1.1))
      = (((d.filter (hsearch_lazy_isLive s.queued)).map Prod.fst).map Prod.fst) by
    simp [List.map_map, Function.comp_def]]
  refine List.map_mergeSort ?_
  intro a ha b hb
  have ha' : a = (a.1, s.orderMap.getD a.1 s.orderDefault) := Prod.ext rfl (hkey a ha)
  have hb' : b = (b.1, s.orderMap.getD b.1 s.orderDefault) := Prod.ext rfl (hkey b hb)
  calc hsearch_lazy_key_le heur a b
      = hsearch_lazy_key_le heur (a.1, s.orderMap.getD a.1 s.orderDefault)
          (b.1, s.orderMap.getD b.1 s.orderDefault) := by rw [← ha', ← hb']
    _ = hsearch_queue_le heur (fun v => s.orderMap.getD v s.orderDefault) a.1 b.1 := rfl

/-!
### The sorted list of the heap
-/

/-- The entries of the heap, in queue order (live and stale). -/
abbrev hsearch_lazy_sorted (s : hsearch_lazy_state V heur) : List (LazyEntry V) :=
  HeapQueue.sortedList (hsearch_lazy_key_le heur) s.heap

omit [LawfulBEq V] in
theorem hsearch_lazy_sorted_perm (s : hsearch_lazy_state V heur) :
    (hsearch_lazy_sorted heur s).Perm s.heap.elems :=
  HeapQueue.sortedList_perm _ _

omit [LawfulBEq V] in
theorem hsearch_lazy_sorted_nodup (s : hsearch_lazy_state V heur) :
    ((hsearch_lazy_sorted heur s).map Prod.snd).Nodup :=
  (((hsearch_lazy_sorted_perm heur s).map Prod.snd).nodup_iff).mpr s.seq_nodup

omit [LawfulBEq V] in
theorem hsearch_lazy_sorted_pairwise (s : hsearch_lazy_state V heur) :
    (hsearch_lazy_sorted heur s).Pairwise (fun a b => hsearch_lazy_le heur a b = true) :=
  HeapQueue.sortedList_pairwise _ (hsearch_lazy_key_le_trans heur)
    (hsearch_lazy_key_le_total heur) _

omit [LawfulBEq V] in
/-- The root of the heap is the first entry of the queue. -/
theorem hsearch_lazy_sorted_eq_cons (s : hsearch_lazy_state V heur) (root : LazyEntry V)
    (hp : s.heap.peek = some root) : ∃ T, hsearch_lazy_sorted heur s = root :: T :=
  HeapQueue.sortedList_head _ (hsearch_lazy_key_le_trans heur) (hsearch_lazy_key_le_total heur)
    s.heap root s.heap_ordered s.seq_nodup hp

end

/-!
## The queue at the root
-/

section

variable (heur : V → ℕ∞) (s : hsearch_lazy_state V heur) (root : LazyEntry V)
  (T : List (LazyEntry V))

/-- The tail of the queue: the vertices of the live entries below the root. -/
def hsearch_lazy_tail : List V :=
  (T.filter (hsearch_lazy_isLive s.queued)).map (fun e => e.1.1)

variable (hp : s.heap.peek = some root)
  (hlive : hsearch_lazy_isLive s.queued root = true)
  (hT : hsearch_lazy_sorted heur s = root :: T)

include hp hlive hT

omit [LawfulBEq V] hp in
/-- **The queue of the state, decomposed at the root.** -/
theorem hsearch_lazy_queue_cons :
    s.queue = root.1.1 :: hsearch_lazy_tail heur s T := by
  show (HeapQueue.liveQueue _ _ _).map Prod.fst = _
  unfold HeapQueue.liveQueue
  rw [show HeapQueue.sortedList (hsearch_lazy_key_le heur) s.heap = root :: T from hT]
  simp [hlive, hsearch_lazy_tail]

omit [LawfulBEq V] hp hlive in
/-- An entry of `T` is not the root. -/
theorem hsearch_lazy_ne_root_of_mem_tail (e : LazyEntry V) (he : e ∈ T) : e.2 ≠ root.2 := by
  have hnd := hsearch_lazy_sorted_nodup heur s
  rw [hT] at hnd
  simp only [List.map_cons, List.nodup_cons, List.mem_map] at hnd
  intro h
  exact hnd.1 ⟨e, he, h⟩

/-- **The `O(1)` queue-membership test.**  A vertex is in the tail of the queue exactly when
the queue map, with the expanded node removed, contains it. -/
theorem hsearch_lazy_qtail_contains_iff (v : V) :
    (s.queued.erase root.1.1).contains v = true ↔ v ∈ hsearch_lazy_tail heur s T := by
  constructor
  · intro hc
    rw [Std.HashMap.contains_erase, Bool.and_eq_true] at hc
    have hne : ¬ (root.1.1 = v) := by
      have := hc.1
      simpa using this
    obtain ⟨n, hn⟩ : ∃ n, s.queued[v]? = some n := by
      rcases hq : s.queued[v]? with _ | n
      · have := hc.2
        rw [Std.HashMap.contains_eq_isSome_getElem?, hq] at this
        exact absurd this (by simp)
      · exact ⟨n, rfl⟩
    obtain ⟨e, he, hev, hen⟩ := s.queued_live v n hn
    have hlive_e : hsearch_lazy_isLive s.queued e = true := by
      rw [hsearch_lazy_isLive_iff, hev, hen, hn]
    have hmem : e ∈ root :: T := by
      rw [← hT]
      exact (hsearch_lazy_sorted_perm heur s).mem_iff.mpr he
    rcases List.mem_cons.mp hmem with rfl | hT'
    · exact absurd hev hne
    · exact List.mem_map.mpr ⟨e, List.mem_filter.mpr ⟨hT', hlive_e⟩, hev⟩
  · intro hmem
    obtain ⟨e, hef, hev⟩ := List.mem_map.mp hmem
    have heT := (List.mem_filter.mp hef).1
    have hlive_e := (hsearch_lazy_isLive_iff s.queued e).mp (List.mem_filter.mp hef).2
    rw [hev] at hlive_e
    have hne : ¬ (root.1.1 = v) := by
      intro h
      have hroot := (hsearch_lazy_isLive_iff s.queued root).mp hlive
      rw [h, hlive_e] at hroot
      exact hsearch_lazy_ne_root_of_mem_tail heur s root T hT e heT (Option.some.inj hroot)
    rw [Std.HashMap.contains_erase, Std.HashMap.contains_eq_isSome_getElem?, hlive_e]
    simpa using hne

end

/-!
## The per-neighbour data
-/

section

variable (G : NatGraphWithGenerator V) (heur : V → ℕ∞) (s : hsearch_lazy_state V heur)
  (root : LazyEntry V) (T : List (LazyEntry V))
  (hp : s.heap.peek = some root)
  (hlive : hsearch_lazy_isLive s.queued root = true)
  (hT : hsearch_lazy_sorted heur s = root :: T)

include hp hlive hT

/-- The per-neighbour data is the one of `HeuristicSearchFast`: the two differ only in how
the test `v ∉ stackTail` is performed. -/
theorem hsearch_lazy_items_eq :
    hsearch_lazy_items G heur s root.1.1 (s.queued.erase root.1.1)
      = hsearch_fast_items G heur s.toFastState root.1.1 (hsearch_lazy_tail heur s T) := by
  unfold hsearch_lazy_items hsearch_lazy_itemsOf hsearch_fast_items
  refine List.map_congr_left ?_
  rintro ⟨v, hv⟩ -
  have hc := hsearch_lazy_qtail_contains_iff heur s root T hp hlive hT v
  simp only [hsearch_lazy_state.toFastState]
  by_cases hmem : v ∈ hsearch_lazy_tail heur s T
  · simp only [hc.mpr hmem, hmem, decide_false, Bool.not_true, Bool.false_and,
      not_true_eq_false]
    rfl
  · have : (s.queued.erase root.1.1).contains v = false := by
      simpa using fun h => hmem (hc.mp h)
    simp only [this, hmem, decide_true, Bool.not_false, not_false_eq_true]
    rfl

/-- The path order after the expansion, as computed by `HeuristicSearchMap`. -/
theorem hsearch_lazy_new_order_eq (v : V) :
    hsearch_lazy_new_order G heur s root.1.1 (s.queued.erase root.1.1) v
      = hsearch_new_order (s.toFastState.toMapState.toBaseG G) root.1.1 v := by
  unfold hsearch_lazy_new_order hsearch_lazy_orderMap
  rw [hsearch_lazy_items_eq G heur s root T hp hlive hT,
    hsearch_fast_items_eq G heur s.toFastState root.1.1 (hsearch_lazy_tail heur s T)]
  exact hsearch_map_orderMap_getD G heur s.toFastState.toMapState root.1.1
    (hsearch_lazy_tail heur s T) v

end

/-!
## The items, the newly queued nodes and the decrease-keys
-/

section

variable (G : NatGraphWithGenerator V) (heur : V → ℕ∞) (s : hsearch_lazy_state V heur)
  (head : V) (qt : Std.HashMap V ℕ)

omit [LawfulBEq V] in
/-- The keys of the per-neighbour data are the neighbours of the expanded node. -/
theorem hsearch_lazy_items_keys :
    (hsearch_lazy_items G heur s head qt).map Prod.fst = G.neighbours head := by
  simp [hsearch_lazy_items, hsearch_lazy_itemsOf, List.map_map, Function.comp_def]

omit [LawfulBEq V] in
/-- The vertices of the newly queued entries. -/
theorem hsearch_lazy_newlyKeys_map :
    (hsearch_lazy_newlyKeys G heur s head qt).map Prod.fst
      = hsearch_lazy_newly G heur s head qt := by
  unfold hsearch_lazy_newlyKeys hsearch_lazy_newly
  rw [List.map_filterMap]
  refine List.filterMap_congr fun x _ => ?_
  by_cases h : x.2.2.2 <;> simp [h]

omit [LawfulBEq V] in
/-- The newly queued vertices are pairwise distinct. -/
theorem hsearch_lazy_newly_nodup : (hsearch_lazy_newly G heur s head qt).Nodup := by
  have hsub : ((hsearch_lazy_newly G heur s head qt).map id).Sublist
      ((hsearch_lazy_items G heur s head qt).map Prod.fst) := by
    refine List.map_filterMap_sublist_map _ _ id Prod.fst ?_
    intro a _ b hb
    (by_cases h : a.2.2.2 <;> simp [h] at hb); simp [hb]
  rw [List.map_id] at hsub
  exact ((hsearch_lazy_items_keys G heur s head qt) ▸
    (neighbours_nodup G head)).sublist hsub

omit [LawfulBEq V] in
/-- The vertices of the decrease-keys are pairwise distinct. -/
theorem hsearch_lazy_changedKeys_nodup :
    ((hsearch_lazy_changedKeys G heur s head qt).map Prod.fst).Nodup := by
  have hperm : ((hsearch_lazy_changedKeys G heur s head qt).map Prod.fst).Perm
      ((hsearch_lazy_changedPairs G heur s head qt).map (fun p : LazyKey V × LazyEntry V => p.1.1)) := by
    unfold hsearch_lazy_changedKeys
    rw [List.map_map]
    exact ((List.mergeSort_perm _ _).map (fun p : LazyKey V × LazyEntry V => p.1.1))
  have hsub : ((hsearch_lazy_changedPairs G heur s head qt).map (fun p : LazyKey V × LazyEntry V => p.1.1)).Sublist
      ((hsearch_lazy_items G heur s head qt).map Prod.fst) := by
    unfold hsearch_lazy_changedPairs
    refine List.map_filterMap_sublist_map _ _ (fun p : LazyKey V × LazyEntry V => p.1.1) Prod.fst ?_
    intro a _ b hb
    rcases hq : qt[a.1]? with _ | n
    · rw [hq] at hb; simp at hb
    · rw [hq] at hb
      by_cases hc : a.2.1 == s.orderMap.getD a.1 s.orderDefault
      · simp [hc] at hb
      · simp only [hc, if_false, Bool.false_eq_true] at hb
        obtain rfl : ((a.1, a.2.1), ((a.1, s.orderMap.getD a.1 s.orderDefault), n)) = b :=
          Option.some.inj hb
        rfl
  exact (hperm.nodup_iff).mpr
    (((hsearch_lazy_items_keys G heur s head qt) ▸
      (neighbours_nodup G head)).sublist hsub)

/-- A decrease-key concerns a vertex that is still in the queue. -/
theorem hsearch_lazy_changed_qt (v : V)
    (hv : v ∈ (hsearch_lazy_changedKeys G heur s head qt).map Prod.fst) :
    qt.contains v = true := by
  have hv' : v ∈ (hsearch_lazy_changedPairs G heur s head qt).map (fun p : LazyKey V × LazyEntry V => p.1.1) := by
    have hperm : ((hsearch_lazy_changedKeys G heur s head qt).map Prod.fst).Perm
        ((hsearch_lazy_changedPairs G heur s head qt).map (fun p : LazyKey V × LazyEntry V => p.1.1)) := by
      unfold hsearch_lazy_changedKeys
      rw [List.map_map]
      exact ((List.mergeSort_perm _ _).map (fun p : LazyKey V × LazyEntry V => p.1.1))
    exact hperm.mem_iff.mp hv
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hv'
  obtain ⟨a, _, hab⟩ := List.mem_filterMap.mp hb
  rcases hq : qt[a.1]? with _ | n
  · rw [hq] at hab; simp at hab
  · rw [hq] at hab
    by_cases hc : a.2.1 == s.orderMap.getD a.1 s.orderDefault
    · simp [hc] at hab
    · simp only [hc, if_false, Bool.false_eq_true] at hab
      obtain rfl : ((a.1, a.2.1), ((a.1, s.orderMap.getD a.1 s.orderDefault), n)) = b :=
        Option.some.inj hab
      simp only [Std.HashMap.contains_eq_isSome_getElem?, hq]
      rfl

/-- A newly queued vertex is not in the queue yet. -/
theorem hsearch_lazy_newly_not_qt (hqt : qt = s.queued.erase head) (v : V)
    (hv : v ∈ hsearch_lazy_newly G heur s head qt) : qt.contains v = false := by
  unfold hsearch_lazy_newly at hv
  obtain ⟨x, hx, hxv⟩ := List.mem_filterMap.mp hv
  by_cases hnew : x.2.2.2
  · rw [if_pos hnew] at hxv
    obtain rfl : x.1 = v := Option.some.inj hxv
    simp only [hsearch_lazy_items, hsearch_lazy_itemsOf, List.mem_map, List.mem_attach,
      true_and] at hx
    obtain ⟨⟨u, hu⟩, rfl⟩ := hx
    simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at hnew
    rcases hnew.2 with hvis | hcond
    · -- the vertex has not been visited, so it cannot be queued
      have hnotvis : u ∉ s.vis.toFinset := by
        have := VisitedSet.contains_eq s.vis u
        rw [hvis] at this
        simpa using this.symm
      have hq : s.queued.contains u = false := by
        by_contra hc
        exact hnotvis (s.queued_visited u (by simpa using hc))
      rw [hqt, Std.HashMap.contains_erase, hq]
      simp
    · exact hcond.1
  · rw [if_neg hnew] at hxv
    exact absurd hxv (by simp)

/-- The vertices the expansion pushes are pairwise distinct. -/
theorem hsearch_lazy_pushKeys_nodup' (hqt : qt = s.queued.erase head) :
    ((hsearch_lazy_pushKeys G heur s head qt).map Prod.fst).Nodup := by
  unfold hsearch_lazy_pushKeys
  rw [List.map_append]
  refine List.Nodup.append (hsearch_lazy_changedKeys_nodup G heur s head qt) ?_ ?_
  · rw [hsearch_lazy_newlyKeys_map]
    exact hsearch_lazy_newly_nodup G heur s head qt
  · intro a ha hb
    rw [hsearch_lazy_newlyKeys_map] at hb
    have h1 := hsearch_lazy_changed_qt G heur s head qt a ha
    have h2 := hsearch_lazy_newly_not_qt G heur s head qt hqt a hb
    rw [h1] at h2
    exact absurd h2 (by simp)

omit [LawfulBEq V] in
/-- The vertices of the pushed entries. -/
theorem hsearch_lazy_pushEntries_map :
    (hsearch_lazy_pushEntries G heur s head qt).map (fun e => e.1.1)
      = (hsearch_lazy_pushKeys G heur s head qt).map Prod.fst := by
  unfold hsearch_lazy_pushEntries
  rw [show (fun e : LazyEntry V => e.1.1) = (Prod.fst ∘ Prod.fst) from rfl, ← List.map_map,
    List.zipIdx_map_fst]


/-- The queue map after the expansion, on a pushed vertex. -/
theorem hsearch_lazy_newQueued_pushed (hqt : qt = s.queued.erase head) (e : LazyEntry V)
    (he : e ∈ hsearch_lazy_pushEntries G heur s head qt) :
    (hsearch_lazy_newQueued G heur s head qt)[e.1.1]? = some e.2 := by
  unfold hsearch_lazy_newQueued
  refine Std.HashMap.getElem?_foldl_insert_of_mem (fun e : LazyEntry V => e.1.1)
    (fun e : LazyEntry V => e.2) _ ?_ qt e he
  rw [hsearch_lazy_pushEntries_map]
  exact hsearch_lazy_pushKeys_nodup' G heur s head qt hqt

/-- The queue map after the expansion, on a vertex that is not pushed. -/
theorem hsearch_lazy_newQueued_not_pushed (v : V)
    (hv : v ∉ (hsearch_lazy_pushKeys G heur s head qt).map Prod.fst) :
    (hsearch_lazy_newQueued G heur s head qt)[v]? = qt[v]? := by
  unfold hsearch_lazy_newQueued
  refine Std.HashMap.getElem?_foldl_insert_of_not_mem (fun e : LazyEntry V => e.1.1)
    (fun e : LazyEntry V => e.2) _ qt v ?_
  rw [hsearch_lazy_pushEntries_map]
  exact hv

omit [LawfulBEq V] in
/-- The heap after the expansion is a heap.  The comparison function does not depend on the
state, so — unlike for the eagerly updated heap — this needs nothing but the fact that
insertion and `deleteMin` preserve the invariant. -/
theorem hsearch_lazy_newHeap_ordered :
    LHeap.Ordered (hsearch_lazy_le heur) (hsearch_lazy_newHeap G heur s head qt) :=
  LHeap.Ordered_foldl_insert _ (hsearch_lazy_le_total heur) (hsearch_lazy_le_trans heur) _ _
    (LHeap.Ordered_deleteMin _ (hsearch_lazy_le_total heur) (hsearch_lazy_le_trans heur)
      s.heap s.heap_ordered)

end

/-!
## The entries after the expansion
-/

section

variable (G : NatGraphWithGenerator V) (heur : V → ℕ∞) (s : hsearch_lazy_state V heur)
  (root : LazyEntry V) (T : List (LazyEntry V))
  (hp : s.heap.peek = some root)
  (hT : hsearch_lazy_sorted heur s = root :: T)

include hp hT

omit [LawfulBEq V] in
/-- Removing the root leaves the rest of the queue. -/
theorem hsearch_lazy_deleteMin_perm :
    (LHeap.deleteMin (hsearch_lazy_le heur) s.heap).elems.Perm T := by
  have h1 : s.heap.elems.Perm (root :: (LHeap.deleteMin (hsearch_lazy_le heur) s.heap).elems) :=
    LHeap.elems_deleteMin _ s.heap root hp
  have h2 : s.heap.elems.Perm (root :: T) := by
    refine (hsearch_lazy_sorted_perm heur s).symm.trans ?_
    rw [hT]
  exact (List.Perm.cons_inv (h1.symm.trans h2))

omit [LawfulBEq V] hp hT in
/-- Every entry below the root is an entry of the heap. -/
theorem hsearch_lazy_mem_of_mem_tail (hT : hsearch_lazy_sorted heur s = root :: T)
    (e : LazyEntry V) (he : e ∈ T) : e ∈ s.heap.elems := by
  refine (hsearch_lazy_sorted_perm heur s).mem_iff.mp ?_
  rw [hT]
  exact List.mem_cons_of_mem _ he

omit [LawfulBEq V] in
/-- The entries of the heap after the expansion. -/
theorem hsearch_lazy_newHeap_perm (qt : Std.HashMap V ℕ) :
    (hsearch_lazy_newHeap G heur s root.1.1 qt).elems.Perm
      (T ++ hsearch_lazy_pushEntries G heur s root.1.1 qt) := by
  refine (LHeap.elems_foldl_insert _ _ _).trans ?_
  exact (hsearch_lazy_deleteMin_perm heur s root T hp hT).append_right _

omit [LawfulBEq V] in
/-- The insertion numbers after the expansion are still pairwise distinct. -/
theorem hsearch_lazy_newHeap_nodup (qt : Std.HashMap V ℕ) :
    ((hsearch_lazy_newHeap G heur s root.1.1 qt).elems.map Prod.snd).Nodup := by
  refine (((hsearch_lazy_newHeap_perm G heur s root T hp hT qt).map Prod.snd).nodup_iff).mpr ?_
  rw [List.map_append]
  refine List.Nodup.append ?_ ?_ ?_
  · have hnd := hsearch_lazy_sorted_nodup heur s
    rw [hT, List.map_cons] at hnd
    exact hnd.of_cons
  · unfold hsearch_lazy_pushEntries
    have hpw : ((hsearch_lazy_pushKeys G heur s root.1.1 qt).zipIdx s.nextSeq).Pairwise
        (fun a b => a.2 ≠ b.2) :=
      (SortAux.zipIdx_pairwise_snd_lt _ s.nextSeq).imp (fun h => Nat.ne_of_lt h)
    exact List.pairwise_map.mpr hpw
  · intro a ha hb
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp ha
    obtain ⟨f, hf, hfe⟩ := List.mem_map.mp hb
    have h1 : e.2 < s.nextSeq :=
      s.seq_lt e (hsearch_lazy_mem_of_mem_tail heur s root T hT e he)
    have h2 : s.nextSeq ≤ f.2 := (SortAux.mem_zipIdx_bounds hf).1
    omega

omit [LawfulBEq V] in
/-- The insertion numbers after the expansion are below the new counter. -/
theorem hsearch_lazy_newHeap_seq_lt (qt : Std.HashMap V ℕ) :
    ∀ e ∈ (hsearch_lazy_newHeap G heur s root.1.1 qt).elems,
      e.2 < s.nextSeq + (hsearch_lazy_pushEntries G heur s root.1.1 qt).length := by
  intro e he
  have hmem := (hsearch_lazy_newHeap_perm G heur s root T hp hT qt).mem_iff.mp he
  rcases List.mem_append.mp hmem with h | h
  · have := s.seq_lt e (hsearch_lazy_mem_of_mem_tail heur s root T hT e h)
    omega
  · have := (SortAux.mem_zipIdx_bounds (l := hsearch_lazy_pushKeys G heur s root.1.1 qt)
      (n := s.nextSeq) (p := e) h).2
    simpa [hsearch_lazy_pushEntries] using this

end

end NatGraph
