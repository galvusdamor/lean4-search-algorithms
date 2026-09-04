import SearchAlgorithms.HeuristicSearchHeapLazy

/-!
# The queue after one expansion of the lazily deleted heap

`SearchAlgorithms.HeuristicSearchHeapLazy` established the book-keeping facts about one
expansion of the `heap_lazy` search.  This module puts them together and proves the heart of
the correctness transfer:

`hsearch_lazy_D_ref` is the list of *live* entries of the new heap, listed in the order in
which the reference implementation feeds the new queue to `List.mergeSort` — the old queue
(with every re-inserted node in the place of its now stale entry) followed by the newly
queued nodes.  The four lemmas

* `hsearch_lazy_D_ref_map` — its vertices are `tail ++ newly`,
* `hsearch_lazy_D_ref_live` — all of its entries are live after the expansion,
* `hsearch_lazy_D_ref_perm` — together with the entries the expansion made stale it is a
  list of all entries of the new heap,
* `hsearch_lazy_D_ref_tie` — its insertion numbers increase along tied entries,

feed `hsearch_lazy_queue_eq` (i.e. `HeapQueue.liveQueue_eq`) and give
`hsearch_lazy_newHeap_queue`: the queue after the expansion is literally
`(tail ++ newly).mergeSort …`, the queue of the reference implementation.
-/

namespace NatGraph

open WeightedDiGraph
open SearchAlgorithms

variable {V : Type} [FinEnum V] [BEq V] [LawfulBEq V] [Hashable V]

/-!
## A decrease-key strictly improves the `f`-value

This is the fact that makes lazy deletion stable: a re-inserted node gets a *fresh* insertion
number, so it sorts after every node it is tied with — which is only correct because before
the decrease its `f`-value was *strictly* larger, so every node it is now tied with really
did stand before it in the queue.
-/

omit [BEq V] [LawfulBEq V] [Hashable V] in
/-- If an expansion changes the path order of an already visited node, it strictly decreases
its `f`-value. -/
theorem hsearch_lazy_new_cost_lt {g : NatGraph V} (ps : hsearch_search_state g) (cur v : V)
    (adj : g.Adj cur v) (heur : V → ℕ∞) (hne : new_cost ps cur v adj ≠ ps.pathOrder v) :
    FValueComp.lt (add_heur v (new_cost ps cur v adj) heur)
      (add_heur v (ps.pathOrder v) heur) = true := by
  unfold new_cost at hne ⊢
  split_ifs at hne ⊢ with h1 h2
  · exact absurd rfl hne
  · exact absurd rfl hne
  · simp only [add_heur, FValueComp.lt, Nat.FValueLT, Prod.lex_def, decide_eq_true_eq]
    rw [not_lt] at h1
    rw [not_and_or, not_lt] at h2
    simp only [ne_eq, Prod.ext_iff, not_and_or] at hne
    simp only [path_val] at h1 h2 hne ⊢
    omega

omit [FinEnum V] [BEq V] [LawfulBEq V] [Hashable V] in
/-- `FValueComp.lt a b` rules out `b ≤ a` in the queue order. -/
theorem hsearch_lazy_key_le_of_lt (heur : V → ℕ∞) (a b : LazyKey V)
    (h : FValueComp.lt (add_heur b.1 b.2 heur) (add_heur a.1 a.2 heur) = true) :
    hsearch_lazy_key_le heur a b = false := by
  unfold hsearch_lazy_key_le
  simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not]
  constructor
  · intro he
    rw [he] at h
    exact absurd h (by simpa using FValueComp.lt_irr _)
  · by_contra hlt
    simp only [Bool.not_eq_false] at hlt
    exact absurd (FValueComp.lt_trans _ _ _ hlt h) (by simpa using FValueComp.lt_irr _)

/-!
## The pieces of one expansion, related to each other
-/

section

variable (G : NatGraphWithGenerator V) (heur : V → ℕ∞) (s : hsearch_lazy_state V heur)
  (head : V) (qt : Std.HashMap V ℕ)

omit [LawfulBEq V] in
/-- The pushed entries split into the re-inserted nodes and the newly queued ones. -/
theorem hsearch_lazy_pushEntries_split :
    hsearch_lazy_pushEntries G heur s head qt
      = (hsearch_lazy_changedKeys G heur s head qt).zipIdx s.nextSeq
        ++ (hsearch_lazy_newlyKeys G heur s head qt).zipIdx
            (s.nextSeq + (hsearch_lazy_changedKeys G heur s head qt).length) := by
  unfold hsearch_lazy_pushEntries hsearch_lazy_pushKeys
  rw [List.zipIdx_append]

omit [LawfulBEq V] in
/-- The vertices the expansion pushes. -/
theorem hsearch_lazy_pushKeys_map :
    (hsearch_lazy_pushKeys G heur s head qt).map Prod.fst
      = hsearch_lazy_changedV G heur s head qt ++ hsearch_lazy_newly G heur s head qt := by
  unfold hsearch_lazy_pushKeys hsearch_lazy_changedV
  rw [List.map_append, hsearch_lazy_newlyKeys_map]


/-- Every vertex the expansion pushes gets a fresh number. -/
theorem hsearch_lazy_newQueued_pushed_ge (hqt : qt = s.queued.erase head) (v : V)
    (hv : v ∈ (hsearch_lazy_pushKeys G heur s head qt).map Prod.fst) :
    ∃ n, (hsearch_lazy_newQueued G heur s head qt)[v]? = some n ∧ s.nextSeq ≤ n := by
  rw [← hsearch_lazy_pushEntries_map] at hv
  obtain ⟨e, he, hev⟩ := List.mem_map.mp hv
  refine ⟨e.2, ?_, ?_⟩
  · rw [← hev]
    exact hsearch_lazy_newQueued_pushed G heur s head qt hqt e he
  · exact (SortAux.mem_zipIdx_bounds (l := hsearch_lazy_pushKeys G heur s head qt)
      (n := s.nextSeq) (p := e) he).1

omit [LawfulBEq V] in
/-- The decrease-keys, spelled out. -/
theorem hsearch_lazy_mem_changedPairs_iff (p : LazyKey V × LazyEntry V) :
    p ∈ hsearch_lazy_changedPairs G heur s head qt ↔
      ∃ x ∈ hsearch_lazy_items G heur s head qt, ∃ n, qt[x.1]? = some n ∧
        x.2.1 ≠ s.orderMap.getD x.1 s.orderDefault ∧
        p = ((x.1, x.2.1), ((x.1, s.orderMap.getD x.1 s.orderDefault), n)) := by
  unfold hsearch_lazy_changedPairs
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨x, hx, hxp⟩
    refine ⟨x, hx, ?_⟩
    rcases hq : qt[x.1]? with _ | n
    · rw [hq] at hxp; simp at hxp
    · rw [hq] at hxp
      by_cases hc : x.2.1 == s.orderMap.getD x.1 s.orderDefault
      · simp [hc] at hxp
      · simp only [hc, Bool.false_eq_true, if_false, Option.some.injEq] at hxp
        exact ⟨n, rfl, by simpa using hc, hxp.symm⟩
  · rintro ⟨x, hx, n, hn, hne, rfl⟩
    refine ⟨x, hx, ?_⟩
    rw [hn]
    have : ¬ (x.2.1 == s.orderMap.getD x.1 s.orderDefault) = true := by simpa using hne
    simp [this]

omit [LawfulBEq V] in
/-- The decrease-keys are a permutation of the sorted decrease-keys. -/
theorem hsearch_lazy_changedSorted_perm :
    (hsearch_lazy_changedSorted G heur s head qt).Perm
      (hsearch_lazy_changedPairs G heur s head qt) :=
  List.mergeSort_perm _ _


omit [LawfulBEq V] in
/-- The two halves of a decrease-key concern the same vertex. -/
theorem hsearch_lazy_changedPairs_fst_eq (p : LazyKey V × LazyEntry V)
    (hp : p ∈ hsearch_lazy_changedPairs G heur s head qt) : p.2.1.1 = p.1.1 := by
  rw [hsearch_lazy_mem_changedPairs_iff] at hp
  obtain ⟨x, hx, n, hn, hne, rfl⟩ := hp
  rfl

omit [LawfulBEq V] in
/-- The vertices of the stale entries of the decrease-keys. -/
theorem hsearch_lazy_changedSorted_snd_fst :
    (hsearch_lazy_changedSorted G heur s head qt).map (fun p => p.2.1.1)
      = hsearch_lazy_changedV G heur s head qt := by
  unfold hsearch_lazy_changedV hsearch_lazy_changedKeys
  rw [List.map_map]
  refine List.map_congr_left ?_
  intro p hp
  exact hsearch_lazy_changedPairs_fst_eq G heur s head qt p
    ((hsearch_lazy_changedSorted_perm G heur s head qt).subset hp)

omit [LawfulBEq V] in
/-- The decrease-keys are sorted by their stale entries, i.e. in queue order. -/
theorem hsearch_lazy_changedSorted_pairwise :
    (hsearch_lazy_changedSorted G heur s head qt).Pairwise
      (fun a b => hsearch_lazy_le heur a.2 b.2 = true) :=
  List.pairwise_mergeSort
    (fun a b c hab hbc => hsearch_lazy_le_trans heur a.2 b.2 c.2 hab hbc)
    (fun a b => hsearch_lazy_le_total heur a.2 b.2) _

omit [LawfulBEq V] in
/-- The vertices the expansion re-inserts. -/
theorem hsearch_lazy_mem_changedV_iff (v : V) :
    v ∈ hsearch_lazy_changedV G heur s head qt ↔
      ∃ p ∈ hsearch_lazy_changedPairs G heur s head qt, p.1.1 = v := by
  unfold hsearch_lazy_changedV hsearch_lazy_changedKeys
  rw [List.map_map]
  constructor
  · intro hv
    obtain ⟨p, hp, hpv⟩ := List.mem_map.mp hv
    exact ⟨p, (hsearch_lazy_changedSorted_perm G heur s head qt).subset hp, hpv⟩
  · rintro ⟨p, hp, rfl⟩
    exact List.mem_map.mpr
      ⟨p, (hsearch_lazy_changedSorted_perm G heur s head qt).mem_iff.mpr hp, rfl⟩

end

/-!
## One expansion at the root of the heap
-/

section

variable (G : NatGraphWithGenerator V) (heur : V → ℕ∞) (s : hsearch_lazy_state V heur)
  (root : LazyEntry V) (T : List (LazyEntry V))
  (hp : s.heap.peek = some root)
  (hlive : hsearch_lazy_isLive s.queued root = true)
  (hT : hsearch_lazy_sorted heur s = root :: T)

include hp hlive hT

omit hp in
/-- A live entry below the root is a live entry of the queue map with the root removed. -/
theorem hsearch_lazy_live_qt (e : LazyEntry V) (he : e ∈ T)
    (hl : hsearch_lazy_isLive s.queued e = true) :
    (s.queued.erase root.1.1)[e.1.1]? = some e.2 := by
  have hl' := (hsearch_lazy_isLive_iff s.queued e).mp hl
  have hne : ¬ (root.1.1 = e.1.1) := by
    intro h
    have hr := (hsearch_lazy_isLive_iff s.queued root).mp hlive
    rw [h, hl'] at hr
    exact hsearch_lazy_ne_root_of_mem_tail heur s root T hT e he (Option.some.inj hr)
  rw [Std.HashMap.getElem?_erase, if_neg (by simpa using hne), hl']

omit [LawfulBEq V] hp hlive in
/-- Entries below the root are pairwise distinct. -/
theorem hsearch_lazy_tail_nodup : T.Nodup := by
  have hnd := hsearch_lazy_sorted_nodup heur s
  rw [hT, List.map_cons, List.nodup_cons] at hnd
  exact List.Nodup.of_map Prod.snd hnd.2

omit hp hlive [LawfulBEq V] in
/-- Entries below the root are in queue order. -/
theorem hsearch_lazy_tail_pairwise :
    T.Pairwise (fun a b => hsearch_lazy_le heur a b = true) := by
  have hpw := hsearch_lazy_sorted_pairwise heur s
  rw [hT] at hpw
  exact hpw.of_cons

/-- Every path order the expansion computes is the new path order. -/
theorem hsearch_lazy_items_order (x : V × ((ℕ × ℕ) × V × Bool))
    (hx : x ∈ hsearch_lazy_items G heur s root.1.1 (s.queued.erase root.1.1)) :
    x.2.1 = hsearch_lazy_new_order G heur s root.1.1 (s.queued.erase root.1.1) x.1 := by
  rw [hsearch_lazy_new_order_eq G heur s root T hp hlive hT]
  rw [hsearch_lazy_items_eq G heur s root T hp hlive hT, hsearch_fast_items_eq] at hx
  exact hsearch_map_items_order G heur s.toFastState.toMapState root.1.1
    (hsearch_lazy_tail heur s T) x hx

/-- A vertex whose path order the expansion changes and which is still in the queue is
re-inserted. -/
theorem hsearch_lazy_mem_changedV (v : V)
    (hq : ((s.queued.erase root.1.1)[v]?).isSome = true)
    (hne : hsearch_lazy_new_order G heur s root.1.1 (s.queued.erase root.1.1) v
      ≠ s.orderMap.getD v s.orderDefault) :
    v ∈ hsearch_lazy_changedV G heur s root.1.1 (s.queued.erase root.1.1) := by
  have hadj : (G.toWeightedDiGraph).Adj root.1.1 v := by
    by_contra hadj
    rw [hsearch_lazy_new_order_eq G heur s root T hp hlive hT,
      hsearch_new_order_of_not_adj _ _ _ hadj] at hne
    exact hne rfl
  have hv : v ∈ G.neighbours root.1.1 := (G.neighbours_are_adj root.1.1 v).mp hadj
  obtain ⟨x, hx, hxv⟩ : ∃ x ∈ hsearch_lazy_items G heur s root.1.1 (s.queued.erase root.1.1),
      x.1 = v := by
    have := hsearch_lazy_items_keys G heur s root.1.1 (s.queued.erase root.1.1)
    rw [← this] at hv
    exact List.mem_map.mp hv
  obtain ⟨n, hn⟩ : ∃ n, (s.queued.erase root.1.1)[v]? = some n := by
    rcases h : (s.queued.erase root.1.1)[v]? with _ | n
    · rw [h] at hq; simp at hq
    · exact ⟨n, rfl⟩
  rw [hsearch_lazy_mem_changedV_iff]
  refine ⟨((x.1, x.2.1), ((x.1, s.orderMap.getD x.1 s.orderDefault), n)), ?_, hxv⟩
  rw [hsearch_lazy_mem_changedPairs_iff]
  refine ⟨x, hx, n, by rw [hxv]; exact hn, ?_, rfl⟩
  rw [hsearch_lazy_items_order G heur s root T hp hlive hT x hx, hxv]
  exact hne

/-- A re-inserted vertex is a neighbour whose path order really changed. -/
theorem hsearch_lazy_changedV_order (v : V)
    (hv : v ∈ hsearch_lazy_changedV G heur s root.1.1 (s.queued.erase root.1.1)) :
    hsearch_lazy_new_order G heur s root.1.1 (s.queued.erase root.1.1) v
      ≠ s.orderMap.getD v s.orderDefault := by
  rw [hsearch_lazy_mem_changedV_iff] at hv
  obtain ⟨p, hp', rfl⟩ := hv
  rw [hsearch_lazy_mem_changedPairs_iff] at hp'
  obtain ⟨x, hx, n, _, hne, rfl⟩ := hp'
  rw [← hsearch_lazy_items_order G heur s root T hp hlive hT x hx]
  exact hne

omit [LawfulBEq V] hp hlive hT in
/-- A re-inserted vertex is a neighbour of the expanded node. -/
theorem hsearch_lazy_changedV_adj (v : V)
    (hv : v ∈ hsearch_lazy_changedV G heur s root.1.1 (s.queued.erase root.1.1)) :
    (G.toWeightedDiGraph).Adj root.1.1 v := by
  rw [hsearch_lazy_mem_changedV_iff] at hv
  obtain ⟨p, hp', rfl⟩ := hv
  rw [hsearch_lazy_mem_changedPairs_iff] at hp'
  obtain ⟨x, hx, n, _, _, rfl⟩ := hp'
  refine (G.neighbours_are_adj root.1.1 x.1).mpr ?_
  rw [← hsearch_lazy_items_keys G heur s root.1.1 (s.queued.erase root.1.1)]
  exact List.mem_map_of_mem hx


omit hp in
/-- The queue map after the expansion, on a live entry that the expansion does not
re-insert. -/
theorem hsearch_lazy_newQueued_of_unchanged (e : LazyEntry V) (he : e ∈ T)
    (hl : hsearch_lazy_isLive s.queued e = true)
    (hc : hsearch_lazy_isChanged G heur s root.1.1 (s.queued.erase root.1.1) e = false) :
    (hsearch_lazy_newQueued G heur s root.1.1 (s.queued.erase root.1.1))[e.1.1]? = some e.2 := by
  have hqt := hsearch_lazy_live_qt heur s root T hlive hT e he hl
  have hnotc : e.1.1 ∉ hsearch_lazy_changedV G heur s root.1.1 (s.queued.erase root.1.1) := by
    simpa [hsearch_lazy_isChanged] using hc
  have hnot : e.1.1 ∉
      (hsearch_lazy_pushKeys G heur s root.1.1 (s.queued.erase root.1.1)).map Prod.fst := by
    rw [hsearch_lazy_pushKeys_map]
    intro hmem
    rcases List.mem_append.mp hmem with h | h
    · exact hnotc h
    · have hcon := hsearch_lazy_newly_not_qt G heur s root.1.1 _ rfl e.1.1 h
      rw [Std.HashMap.contains_eq_isSome_getElem?, hqt] at hcon
      simp at hcon
  rw [hsearch_lazy_newQueued_not_pushed G heur s root.1.1 _ e.1.1 hnot, hqt]

/-- An entry the expansion does not re-insert is unchanged. -/
theorem hsearch_lazy_replace_eq_self (e : LazyEntry V) (he : e ∈ T)
    (hl : hsearch_lazy_isLive s.queued e = true)
    (hc : hsearch_lazy_isChanged G heur s root.1.1 (s.queued.erase root.1.1) e = false) :
    hsearch_lazy_replace G heur s root.1.1 (s.queued.erase root.1.1) e = e := by
  have hqt := hsearch_lazy_live_qt heur s root T hlive hT e he hl
  have hnotc : e.1.1 ∉ hsearch_lazy_changedV G heur s root.1.1 (s.queued.erase root.1.1) := by
    simpa [hsearch_lazy_isChanged] using hc
  have hkey : e.1.2 = s.orderMap.getD e.1.1 s.orderDefault :=
    s.live_key e (hsearch_lazy_mem_of_mem_tail heur s root T hT e he) hl
  have horder : hsearch_lazy_new_order G heur s root.1.1 (s.queued.erase root.1.1) e.1.1
      = s.orderMap.getD e.1.1 s.orderDefault := by
    by_contra hne
    exact hnotc (hsearch_lazy_mem_changedV G heur s root T hp hlive hT e.1.1
      (by rw [hqt]; rfl) hne)
  have hnum : (hsearch_lazy_newQueued G heur s root.1.1
      (s.queued.erase root.1.1)).getD e.1.1 0 = e.2 := by
    rw [Std.HashMap.getD_eq_getD_getElem?,
      hsearch_lazy_newQueued_of_unchanged G heur s root T hlive hT e he hl hc]
    rfl
  unfold hsearch_lazy_replace
  rw [horder, ← hkey, hnum]

omit hp in
/-- **An entry below the root is live after the expansion iff it was live before and the
expansion did not re-insert its vertex.**  In particular a stale entry stays stale. -/
theorem hsearch_lazy_isLive_new (e : LazyEntry V) (he : e ∈ T) :
    hsearch_lazy_isLive (hsearch_lazy_newQueued G heur s root.1.1 (s.queued.erase root.1.1)) e
      = (hsearch_lazy_isLive s.queued e
          && !hsearch_lazy_isChanged G heur s root.1.1 (s.queued.erase root.1.1) e) := by
  have hlt : e.2 < s.nextSeq := s.seq_lt e (hsearch_lazy_mem_of_mem_tail heur s root T hT e he)
  by_cases hpush : e.1.1 ∈
      (hsearch_lazy_pushKeys G heur s root.1.1 (s.queued.erase root.1.1)).map Prod.fst
  · obtain ⟨n, hn, hnge⟩ :=
      hsearch_lazy_newQueued_pushed_ge G heur s root.1.1 (s.queued.erase root.1.1) rfl e.1.1 hpush
    have hfalse : hsearch_lazy_isLive
        (hsearch_lazy_newQueued G heur s root.1.1 (s.queued.erase root.1.1)) e = false := by
      rw [Bool.eq_false_iff, Ne, hsearch_lazy_isLive_iff, hn]
      intro hcon
      have : n = e.2 := Option.some.inj hcon
      omega
    rw [hfalse]
    -- and it is not live-and-unchanged either
    by_cases hl : hsearch_lazy_isLive s.queued e = true
    · by_cases hc : hsearch_lazy_isChanged G heur s root.1.1 (s.queued.erase root.1.1) e = true
      · simp [hc]
      · rw [Bool.not_eq_true] at hc
        have := hsearch_lazy_newQueued_of_unchanged G heur s root T hlive hT e he hl hc
        rw [hn] at this
        have : n = e.2 := Option.some.inj this
        omega
    · rw [Bool.not_eq_true] at hl
      simp [hl]
  · have hnq := hsearch_lazy_newQueued_not_pushed G heur s root.1.1
      (s.queued.erase root.1.1) e.1.1 hpush
    have hnotc : e.1.1 ∉ hsearch_lazy_changedV G heur s root.1.1 (s.queued.erase root.1.1) := by
      intro h
      exact hpush (by rw [hsearch_lazy_pushKeys_map]; exact List.mem_append_left _ h)
    have hc : hsearch_lazy_isChanged G heur s root.1.1 (s.queued.erase root.1.1) e = false := by
      simpa [hsearch_lazy_isChanged] using hnotc
    rw [hc]
    simp only [Bool.not_false, Bool.and_true]
    by_cases hl : hsearch_lazy_isLive s.queued e = true
    · rw [hl, hsearch_lazy_isLive_iff, hnq,
        hsearch_lazy_live_qt heur s root T hlive hT e he hl]
    · rw [Bool.not_eq_true] at hl
      rw [hl, Bool.eq_false_iff, Ne, hsearch_lazy_isLive_iff, hnq,
        Std.HashMap.getElem?_erase]
      split
      · simp
      · rw [Bool.eq_false_iff, Ne, hsearch_lazy_isLive_iff] at hl
        exact hl

omit hp in
/-- The entries below the root that are live after the expansion. -/
theorem hsearch_lazy_filter_isLive_new :
    T.filter (hsearch_lazy_isLive
        (hsearch_lazy_newQueued G heur s root.1.1 (s.queued.erase root.1.1)))
      = (T.filter (hsearch_lazy_isLive s.queued)).filter
          (fun e => !hsearch_lazy_isChanged G heur s root.1.1 (s.queued.erase root.1.1) e) := by
  rw [List.filter_filter]
  refine List.filter_congr ?_
  intro e he
  rw [hsearch_lazy_isLive_new G heur s root T hlive hT e he, Bool.and_comm]


/-- **The stale entries of the decrease-keys are exactly the live entries below the root
whose vertex the expansion re-inserts, in queue order.**  This is the step that makes the
lazy queue reproduce the tie-breaking of the reference implementation's stable sort. -/
theorem hsearch_lazy_changedSorted_snd_eq :
    (hsearch_lazy_changedSorted G heur s root.1.1 (s.queued.erase root.1.1)).map Prod.snd
      = (T.filter (hsearch_lazy_isLive s.queued)).filter
          (hsearch_lazy_isChanged G heur s root.1.1 (s.queued.erase root.1.1)) := by
  -- a decrease-key comes from a live entry below the root
  have hfwd : ∀ p ∈ hsearch_lazy_changedPairs G heur s root.1.1 (s.queued.erase root.1.1),
      p.2 ∈ T ∧ hsearch_lazy_isLive s.queued p.2 = true := by
    intro p hpm
    rw [hsearch_lazy_mem_changedPairs_iff] at hpm
    obtain ⟨x, hx, n, hn, hne, rfl⟩ := hpm
    have hne_root : ¬ (root.1.1 = x.1) := by
      intro h
      rw [Std.HashMap.getElem?_erase, if_pos (by simpa using h)] at hn
      simp at hn
    have hq : s.queued[x.1]? = some n := by
      rwa [Std.HashMap.getElem?_erase, if_neg (by simpa using hne_root)] at hn
    obtain ⟨e, hem, hev, hen⟩ := s.queued_live x.1 n hq
    have hlive_e : hsearch_lazy_isLive s.queued e = true := by
      rw [hsearch_lazy_isLive_iff, hev, hen, hq]
    have hkey : e.1.2 = s.orderMap.getD e.1.1 s.orderDefault := s.live_key e hem hlive_e
    have h1 : e.1 = (x.1, s.orderMap.getD x.1 s.orderDefault) := by
      rw [← hev]; exact Prod.ext rfl hkey
    have heq : e = ((x.1, s.orderMap.getD x.1 s.orderDefault), n) := Prod.ext h1 hen
    have hmemT : e ∈ T := by
      have hmem : e ∈ root :: T := by
        rw [← hT]; exact (hsearch_lazy_sorted_perm heur s).mem_iff.mpr hem
      rcases List.mem_cons.mp hmem with rfl | h
      · exact absurd hev hne_root
      · exact h
    rw [← heq]
    exact ⟨hmemT, hlive_e⟩
  -- and conversely
  have hre : ∀ e ∈ T, hsearch_lazy_isLive s.queued e = true →
      hsearch_lazy_isChanged G heur s root.1.1 (s.queued.erase root.1.1) e = true →
      e ∈ (hsearch_lazy_changedSorted G heur s root.1.1
        (s.queued.erase root.1.1)).map Prod.snd := by
    intro e he hl hc
    have hv : e.1.1 ∈ hsearch_lazy_changedV G heur s root.1.1 (s.queued.erase root.1.1) := by
      simpa [hsearch_lazy_isChanged] using hc
    rw [hsearch_lazy_mem_changedV_iff] at hv
    obtain ⟨p, hpm, hpv⟩ := hv
    have hchar := (hsearch_lazy_mem_changedPairs_iff G heur s root.1.1
      (s.queued.erase root.1.1) p).mp hpm
    obtain ⟨x, hx, n, hn, hne, rfl⟩ := hchar
    simp only at hpv
    rw [hpv] at hn
    have hq := hsearch_lazy_live_qt heur s root T hlive hT e he hl
    have hn2 : n = e.2 := Option.some.inj (hn.symm.trans hq)
    have hkey : e.1.2 = s.orderMap.getD e.1.1 s.orderDefault :=
      s.live_key e (hsearch_lazy_mem_of_mem_tail heur s root T hT e he) hl
    refine List.mem_map.mpr ⟨((x.1, x.2.1), ((x.1, s.orderMap.getD x.1 s.orderDefault), n)),
      (hsearch_lazy_changedSorted_perm G heur s root.1.1
        (s.queued.erase root.1.1)).mem_iff.mpr hpm, ?_⟩
    simp only
    rw [hpv, hn2, ← hkey]
  -- the numbers below the root are pairwise distinct
  have hTnd : (T.map Prod.snd).Nodup := by
    have hnd := hsearch_lazy_sorted_nodup heur s
    rw [hT, List.map_cons, List.nodup_cons] at hnd
    exact hnd.2
  have hRnd : ((((T.filter (hsearch_lazy_isLive s.queued)).filter
      (hsearch_lazy_isChanged G heur s root.1.1 (s.queued.erase root.1.1)))).map
        Prod.snd).Nodup :=
    hTnd.sublist (List.Sublist.map _ (List.filter_sublist.trans List.filter_sublist))
  have hR : (((T.filter (hsearch_lazy_isLive s.queued)).filter
      (hsearch_lazy_isChanged G heur s root.1.1 (s.queued.erase root.1.1)))).Nodup :=
    List.Nodup.of_map Prod.snd hRnd
  have hL : ((hsearch_lazy_changedSorted G heur s root.1.1
      (s.queued.erase root.1.1)).map Prod.snd).Nodup := by
    refine List.Nodup.of_map (fun e : LazyEntry V => e.1.1) ?_
    rw [List.map_map,
      show ((fun e : LazyEntry V => e.1.1) ∘
          (Prod.snd : LazyKey V × LazyEntry V → LazyEntry V))
        = (fun p : LazyKey V × LazyEntry V => p.2.1.1) from rfl,
      hsearch_lazy_changedSorted_snd_fst]
    simpa [hsearch_lazy_changedV] using
      hsearch_lazy_changedKeys_nodup G heur s root.1.1 (s.queued.erase root.1.1)
  have hperm : ((hsearch_lazy_changedSorted G heur s root.1.1
      (s.queued.erase root.1.1)).map Prod.snd).Perm
      ((T.filter (hsearch_lazy_isLive s.queued)).filter
        (hsearch_lazy_isChanged G heur s root.1.1 (s.queued.erase root.1.1))) := by
    rw [List.perm_ext_iff_of_nodup hL hR]
    intro a
    constructor
    · intro ha
      obtain ⟨q, hqm, rfl⟩ := List.mem_map.mp ha
      have hqm' := (hsearch_lazy_changedSorted_perm G heur s root.1.1
        (s.queued.erase root.1.1)).subset hqm
      obtain ⟨h1, h2⟩ := hfwd q hqm'
      refine List.mem_filter.mpr ⟨List.mem_filter.mpr ⟨h1, h2⟩, ?_⟩
      have : q.2.1.1 ∈ hsearch_lazy_changedV G heur s root.1.1 (s.queued.erase root.1.1) := by
        rw [hsearch_lazy_changedPairs_fst_eq G heur s root.1.1 (s.queued.erase root.1.1) q hqm',
          hsearch_lazy_mem_changedV_iff]
        exact ⟨q, hqm', rfl⟩
      simpa [hsearch_lazy_isChanged] using this
    · intro ha
      obtain ⟨ha1, hc⟩ := List.mem_filter.mp ha
      obtain ⟨he, hl⟩ := List.mem_filter.mp ha1
      exact hre a he hl hc
  refine SortAux.eq_of_perm_of_zipIdxLE (hsearch_lazy_key_le heur) _ _ hperm ?_ ?_
    ((hperm.map Prod.snd).nodup_iff.mpr hRnd)
  · exact List.pairwise_map.mpr
      (hsearch_lazy_changedSorted_pairwise G heur s root.1.1 (s.queued.erase root.1.1))
  · exact (hsearch_lazy_tail_pairwise heur s root T hT).sublist
      (List.filter_sublist.trans List.filter_sublist)


/-- **The re-inserted entries, in queue order and with the numbers the expansion gives
them.** -/
theorem hsearch_lazy_changed_replace :
    ((T.filter (hsearch_lazy_isLive s.queued)).filter
        (hsearch_lazy_isChanged G heur s root.1.1 (s.queued.erase root.1.1))).map
      (hsearch_lazy_replace G heur s root.1.1 (s.queued.erase root.1.1))
      = (hsearch_lazy_changedKeys G heur s root.1.1 (s.queued.erase root.1.1)).zipIdx
          s.nextSeq := by
  have hfun : ∀ q ∈ hsearch_lazy_changedSorted G heur s root.1.1 (s.queued.erase root.1.1),
      (hsearch_lazy_replace G heur s root.1.1 (s.queued.erase root.1.1) ∘ Prod.snd) q
        = (Prod.fst q,
            (hsearch_lazy_newQueued G heur s root.1.1 (s.queued.erase root.1.1)).getD q.1.1 0) := by
    intro q hq
    have hq' := (hsearch_lazy_changedSorted_perm G heur s root.1.1
      (s.queued.erase root.1.1)).subset hq
    have hchar := (hsearch_lazy_mem_changedPairs_iff G heur s root.1.1
      (s.queued.erase root.1.1) q).mp hq'
    obtain ⟨x, hx, n, hn, hne, rfl⟩ := hchar
    simp only [Function.comp_apply, hsearch_lazy_replace]
    rw [← hsearch_lazy_items_order G heur s root T hp hlive hT x hx]
  rw [← hsearch_lazy_changedSorted_snd_eq G heur s root T hp hlive hT, List.map_map,
    List.map_congr_left hfun]
  refine List.map_pair_eq_zipIdx _ Prod.fst
    (fun q : LazyKey V × LazyEntry V =>
      (hsearch_lazy_newQueued G heur s root.1.1 (s.queued.erase root.1.1)).getD q.1.1 0)
    s.nextSeq ?_
  intro i hi
  have hlen : i <
      (hsearch_lazy_changedKeys G heur s root.1.1 (s.queued.erase root.1.1)).length := by
    simpa [hsearch_lazy_changedKeys] using hi
  have hlen2 : i <
      (hsearch_lazy_pushEntries G heur s root.1.1 (s.queued.erase root.1.1)).length := by
    simp only [hsearch_lazy_pushEntries, List.length_zipIdx, hsearch_lazy_pushKeys,
      List.length_append]
    omega
  have hget : (hsearch_lazy_pushEntries G heur s root.1.1 (s.queued.erase root.1.1))[i]
      = ((hsearch_lazy_changedKeys G heur s root.1.1 (s.queued.erase root.1.1))[i],
          s.nextSeq + i) := by
    simp only [hsearch_lazy_pushEntries]
    rw [List.getElem_zipIdx]
    congr 1
    simp only [hsearch_lazy_pushKeys]
    exact List.getElem_append_left hlen
  have hmem := List.getElem_mem hlen2
  rw [hget] at hmem
  have hval := hsearch_lazy_newQueued_pushed G heur s root.1.1 (s.queued.erase root.1.1) rfl _ hmem
  simp only [hsearch_lazy_changedKeys, List.getElem_map] at hval
  simp only [Std.HashMap.getD_eq_getD_getElem?, hval]
  rfl


/-- **A decrease-key strictly improves the queue order of its vertex.**  This is why giving
the re-inserted entry a *fresh* (hence large) number is correct: every entry it is tied with
after the decrease stood strictly before it in the old queue. -/
theorem hsearch_lazy_changed_key_lt (f : LazyEntry V) (hfT : f ∈ T)
    (hfl : hsearch_lazy_isLive s.queued f = true)
    (hc : hsearch_lazy_isChanged G heur s root.1.1 (s.queued.erase root.1.1) f = true) :
    hsearch_lazy_key_le heur f.1
      (hsearch_lazy_replace G heur s root.1.1 (s.queued.erase root.1.1) f).1 = false := by
  have hv : f.1.1 ∈ hsearch_lazy_changedV G heur s root.1.1 (s.queued.erase root.1.1) := by
    simpa [hsearch_lazy_isChanged] using hc
  have hadj := hsearch_lazy_changedV_adj G heur s root f.1.1 hv
  have hne := hsearch_lazy_changedV_order G heur s root T hp hlive hT f.1.1 hv
  have hvis : f.1.1 ∈ s.vis.toFinset := by
    refine s.queued_visited f.1.1 ?_
    rw [Std.HashMap.contains_eq_isSome_getElem?, (hsearch_lazy_isLive_iff s.queued f).mp hfl]
    rfl
  have hkey : f.1.2 = s.orderMap.getD f.1.1 s.orderDefault :=
    s.live_key f (hsearch_lazy_mem_of_mem_tail heur s root T hT f hfT) hfl
  have hno : hsearch_lazy_new_order G heur s root.1.1 (s.queued.erase root.1.1) f.1.1
      = new_cost (s.toFastState.toMapState.toBaseG G) root.1.1 f.1.1 hadj := by
    rw [hsearch_lazy_new_order_eq G heur s root T hp hlive hT,
      hsearch_new_order_of_adj _ root.1.1 f.1.1 hadj,
      if_neg (by simpa [hsearch_lazy_state.toFastState, hsearch_fast_state.toMapState]
        using hvis)]
  have hlt : FValueComp.lt
      (add_heur f.1.1 (new_cost (s.toFastState.toMapState.toBaseG G) root.1.1 f.1.1 hadj) heur)
      (add_heur f.1.1 ((s.toFastState.toMapState.toBaseG G).pathOrder f.1.1) heur) = true := by
    refine hsearch_lazy_new_cost_lt _ root.1.1 f.1.1 hadj heur ?_
    rw [← hno]
    exact hne
  refine hsearch_lazy_key_le_of_lt heur f.1 _ ?_
  show FValueComp.lt (add_heur f.1.1
      (hsearch_lazy_new_order G heur s root.1.1 (s.queued.erase root.1.1) f.1.1) heur)
    (add_heur f.1.1 f.1.2 heur) = true
  rw [hno, hkey]
  exact hlt

end

/-!
## The live entries after the expansion
-/

section

variable (G : NatGraphWithGenerator V) (heur : V → ℕ∞) (s : hsearch_lazy_state V heur)
  (root : LazyEntry V) (T : List (LazyEntry V))

/-- The live entries after the expansion, in the order in which the reference implementation
feeds them to `mergeSort`: the old queue (with every re-inserted node in the place of its
now stale entry) followed by the newly queued nodes. -/
def hsearch_lazy_D_ref : List (LazyEntry V) :=
  (T.filter (hsearch_lazy_isLive s.queued)).map
      (hsearch_lazy_replace G heur s root.1.1 (s.queued.erase root.1.1))
    ++ ((hsearch_lazy_newlyKeys G heur s root.1.1 (s.queued.erase root.1.1)).zipIdx
        (s.nextSeq + (hsearch_lazy_changedKeys G heur s root.1.1
          (s.queued.erase root.1.1)).length))

omit [LawfulBEq V] in
/-- The vertices of `hsearch_lazy_D_ref` are the queue of the reference implementation. -/
theorem hsearch_lazy_D_ref_map :
    (hsearch_lazy_D_ref G heur s root T).map (fun e => e.1.1)
      = hsearch_lazy_tail heur s T
        ++ hsearch_lazy_newly G heur s root.1.1 (s.queued.erase root.1.1) := by
  unfold hsearch_lazy_D_ref hsearch_lazy_tail
  rw [List.map_append]
  congr 1
  · rw [List.map_map]
    rfl
  · rw [show (fun e : LazyEntry V => e.1.1) = (Prod.fst ∘ Prod.fst) from rfl, ← List.map_map,
      List.zipIdx_map_fst, hsearch_lazy_newlyKeys_map]

variable (hp : s.heap.peek = some root)
  (hlive : hsearch_lazy_isLive s.queued root = true)
  (hT : hsearch_lazy_sorted heur s = root :: T)

include hp hlive hT

/-- Every entry of `hsearch_lazy_D_ref` is live after the expansion. -/
theorem hsearch_lazy_D_ref_live :
    ∀ e ∈ hsearch_lazy_D_ref G heur s root T,
      hsearch_lazy_isLive
        (hsearch_lazy_newQueued G heur s root.1.1 (s.queued.erase root.1.1)) e = true := by
  intro e he
  unfold hsearch_lazy_D_ref at he
  rcases List.mem_append.mp he with h | h
  · obtain ⟨f, hf, rfl⟩ := List.mem_map.mp h
    obtain ⟨hfT, hfl⟩ := List.mem_filter.mp hf
    by_cases hc : hsearch_lazy_isChanged G heur s root.1.1 (s.queued.erase root.1.1) f = true
    · have hv : f.1.1 ∈
          (hsearch_lazy_pushKeys G heur s root.1.1 (s.queued.erase root.1.1)).map Prod.fst := by
        rw [hsearch_lazy_pushKeys_map]
        exact List.mem_append_left _ (by simpa [hsearch_lazy_isChanged] using hc)
      obtain ⟨n, hn, -⟩ := hsearch_lazy_newQueued_pushed_ge G heur s root.1.1
        (s.queued.erase root.1.1) rfl f.1.1 hv
      rw [hsearch_lazy_isLive_iff]
      simp only [hsearch_lazy_replace, Std.HashMap.getD_eq_getD_getElem?, hn]
      rfl
    · rw [Bool.not_eq_true] at hc
      rw [hsearch_lazy_replace_eq_self G heur s root T hp hlive hT f hfT hfl hc,
        hsearch_lazy_isLive_iff]
      exact hsearch_lazy_newQueued_of_unchanged G heur s root T hlive hT f hfT hfl hc
  · have hmem : e ∈ hsearch_lazy_pushEntries G heur s root.1.1 (s.queued.erase root.1.1) := by
      rw [hsearch_lazy_pushEntries_split]
      exact List.mem_append_right _ h
    rw [hsearch_lazy_isLive_iff]
    exact hsearch_lazy_newQueued_pushed G heur s root.1.1 (s.queued.erase root.1.1) rfl e hmem

/-- `hsearch_lazy_D_ref` together with the entries the expansion made stale is a list of all
entries of the new heap. -/
theorem hsearch_lazy_D_ref_perm :
    (hsearch_lazy_newHeap G heur s root.1.1 (s.queued.erase root.1.1)).elems.Perm
      (hsearch_lazy_D_ref G heur s root T
        ++ T.filter (fun e => !hsearch_lazy_isLive
            (hsearch_lazy_newQueued G heur s root.1.1 (s.queued.erase root.1.1)) e)) := by
  have hDL : ((T.filter (hsearch_lazy_isLive s.queued)).map
      (hsearch_lazy_replace G heur s root.1.1 (s.queued.erase root.1.1))).Perm
      (T.filter (hsearch_lazy_isLive
          (hsearch_lazy_newQueued G heur s root.1.1 (s.queued.erase root.1.1)))
        ++ (hsearch_lazy_changedKeys G heur s root.1.1
            (s.queued.erase root.1.1)).zipIdx s.nextSeq) := by
    have hf : ∀ a ∈ T.filter (hsearch_lazy_isLive s.queued),
        hsearch_lazy_isChanged G heur s root.1.1 (s.queued.erase root.1.1) a = false →
        hsearch_lazy_replace G heur s root.1.1 (s.queued.erase root.1.1) a = a := by
      intro a ha hc
      obtain ⟨haT, hal⟩ := List.mem_filter.mp ha
      exact hsearch_lazy_replace_eq_self G heur s root T hp hlive hT a haT hal hc
    refine (List.perm_map_replace _ _ _ hf).trans ?_
    rw [← hsearch_lazy_filter_isLive_new G heur s root T hlive hT,
      hsearch_lazy_changed_replace G heur s root T hp hlive hT]
  have hTperm : T.Perm (T.filter (hsearch_lazy_isLive
        (hsearch_lazy_newQueued G heur s root.1.1 (s.queued.erase root.1.1)))
      ++ T.filter (fun e => !hsearch_lazy_isLive
          (hsearch_lazy_newQueued G heur s root.1.1 (s.queued.erase root.1.1)) e)) :=
    (List.filter_append_perm _ T).symm
  refine (hsearch_lazy_newHeap_perm G heur s root T hp hT (s.queued.erase root.1.1)).trans ?_
  rw [hsearch_lazy_pushEntries_split]
  refine (hTperm.append_right _).trans ?_
  refine List.Perm.trans ?_ (((hDL.symm.append_right _).append_right _))
  exact List.perm_append_rotate _ _ _ _

/-- **The numbers of the live entries break ties the way the stable sort does.**  This is
where the two facts about a decrease-key are used: a re-inserted node gets a fresh number, so
it sorts after everything it is now tied with (`hsearch_lazy_changed_key_lt`); and several
nodes re-inserted by the same expansion are numbered in queue order
(`hsearch_lazy_changedSorted_snd_eq`). -/
theorem hsearch_lazy_D_ref_tie :
    (hsearch_lazy_D_ref G heur s root T).Pairwise
      (fun a b => (hsearch_lazy_key_le heur a.1 b.1 && hsearch_lazy_key_le heur b.1 a.1) = true →
        a.2 ≤ b.2) := by
  have hCK := hsearch_lazy_changed_replace G heur s root T hp hlive hT
  have hbnd : ∀ f ∈ T.filter (hsearch_lazy_isLive s.queued),
      hsearch_lazy_isChanged G heur s root.1.1 (s.queued.erase root.1.1) f = true →
      s.nextSeq ≤ (hsearch_lazy_replace G heur s root.1.1 (s.queued.erase root.1.1) f).2 ∧
      (hsearch_lazy_replace G heur s root.1.1 (s.queued.erase root.1.1) f).2
        < s.nextSeq + (hsearch_lazy_changedKeys G heur s root.1.1
            (s.queued.erase root.1.1)).length := by
    intro f hf hc
    have hmem : hsearch_lazy_replace G heur s root.1.1 (s.queued.erase root.1.1) f
        ∈ (hsearch_lazy_changedKeys G heur s root.1.1 (s.queued.erase root.1.1)).zipIdx
            s.nextSeq := by
      rw [← hCK]
      exact List.mem_map_of_mem (List.mem_filter.mpr ⟨hf, hc⟩)
    exact SortAux.mem_zipIdx_bounds hmem
  have hunch : ∀ f ∈ T.filter (hsearch_lazy_isLive s.queued),
      hsearch_lazy_isChanged G heur s root.1.1 (s.queued.erase root.1.1) f = false →
      hsearch_lazy_replace G heur s root.1.1 (s.queued.erase root.1.1) f = f := by
    intro f hf hc
    obtain ⟨hfT, hfl⟩ := List.mem_filter.mp hf
    exact hsearch_lazy_replace_eq_self G heur s root T hp hlive hT f hfT hfl hc
  unfold hsearch_lazy_D_ref
  refine List.pairwise_append.mpr ⟨?_, ?_, ?_⟩
  · refine List.pairwise_map.mpr ?_
    have h1 : (T.filter (hsearch_lazy_isLive s.queued)).Pairwise
        (fun a b => hsearch_lazy_le heur a b = true) :=
      (hsearch_lazy_tail_pairwise heur s root T hT).sublist List.filter_sublist
    have h2 : (T.filter (hsearch_lazy_isLive s.queued)).Pairwise
        (fun a b => hsearch_lazy_isChanged G heur s root.1.1 (s.queued.erase root.1.1) a = true →
          hsearch_lazy_isChanged G heur s root.1.1 (s.queued.erase root.1.1) b = true →
          (hsearch_lazy_replace G heur s root.1.1 (s.queued.erase root.1.1) a).2
            < (hsearch_lazy_replace G heur s root.1.1 (s.queued.erase root.1.1) b).2) := by
      refine List.pairwise_filter.mp (List.pairwise_map.mp ?_)
      have hmap : List.map (fun b : LazyEntry V =>
            (hsearch_lazy_replace G heur s root.1.1 (s.queued.erase root.1.1) b).2)
          ((T.filter (hsearch_lazy_isLive s.queued)).filter
            (hsearch_lazy_isChanged G heur s root.1.1 (s.queued.erase root.1.1)))
          = ((hsearch_lazy_changedKeys G heur s root.1.1
              (s.queued.erase root.1.1)).zipIdx s.nextSeq).map Prod.snd := by
        rw [← hCK, List.map_map]
        rfl
      rw [hmap]
      exact List.pairwise_map.mpr (SortAux.zipIdx_pairwise_snd_lt _ _)
    refine (h1.and h2).imp_of_mem ?_
    rintro a b ha hb ⟨hle, hlt⟩ htie
    by_cases hca : hsearch_lazy_isChanged G heur s root.1.1 (s.queued.erase root.1.1) a = true
    · by_cases hcb : hsearch_lazy_isChanged G heur s root.1.1 (s.queued.erase root.1.1) b = true
      · exact le_of_lt (hlt hca hcb)
      · exfalso
        rw [Bool.not_eq_true] at hcb
        obtain ⟨haT, hal⟩ := List.mem_filter.mp ha
        rw [Bool.and_eq_true] at htie
        have h1' : hsearch_lazy_key_le heur b.1
            (hsearch_lazy_replace G heur s root.1.1 (s.queued.erase root.1.1) a).1 = true := by
          rw [← hunch b hb hcb]
          exact htie.2
        have h2' : hsearch_lazy_key_le heur a.1 b.1 = true := by
          by_contra hcon
          rw [Bool.not_eq_true] at hcon
          simp [hsearch_lazy_le, List.zipIdxLE, hcon] at hle
        have h3' := hsearch_lazy_key_le_trans heur a.1 b.1 _ h2' h1'
        rw [hsearch_lazy_changed_key_lt G heur s root T hp hlive hT a haT hal hca] at h3'
        exact absurd h3' (by simp)
    · rw [Bool.not_eq_true] at hca
      rw [hunch a ha hca]
      by_cases hcb : hsearch_lazy_isChanged G heur s root.1.1 (s.queued.erase root.1.1) b = true
      · obtain ⟨haT, -⟩ := List.mem_filter.mp ha
        have hs1 : a.2 < s.nextSeq :=
          s.seq_lt a (hsearch_lazy_mem_of_mem_tail heur s root T hT a haT)
        have hs2 := (hbnd b hb hcb).1
        omega
      · rw [Bool.not_eq_true] at hcb
        rw [hunch a ha hca, hunch b hb hcb] at htie
        rw [hunch b hb hcb]
        rw [Bool.and_eq_true] at htie
        simp only [hsearch_lazy_le, List.zipIdxLE, if_pos htie.1, if_pos htie.2,
          decide_eq_true_eq] at hle
        exact hle
  · refine (SortAux.zipIdx_pairwise_snd_lt _ _).imp ?_
    intro x y h _
    omega
  · intro a ha b hb htie
    clear htie
    obtain ⟨f, hf, rfl⟩ := List.mem_map.mp ha
    have h2 : s.nextSeq + (hsearch_lazy_changedKeys G heur s root.1.1
        (s.queued.erase root.1.1)).length ≤ b.2 := (SortAux.mem_zipIdx_bounds hb).1
    by_cases hc : hsearch_lazy_isChanged G heur s root.1.1 (s.queued.erase root.1.1) f = true
    · have h3 := (hbnd f hf hc).2
      omega
    · rw [Bool.not_eq_true] at hc
      rw [hunch f hf hc]
      obtain ⟨hfT, -⟩ := List.mem_filter.mp hf
      have h3 := s.seq_lt f (hsearch_lazy_mem_of_mem_tail heur s root T hT f hfT)
      omega


/-!
### The invariants of the state after the expansion
-/

/-- Every key the expansion pushes carries the new path order of its vertex. -/
theorem hsearch_lazy_pushKeys_order (k : LazyKey V)
    (hk : k ∈ hsearch_lazy_pushKeys G heur s root.1.1 (s.queued.erase root.1.1)) :
    k.2 = hsearch_lazy_new_order G heur s root.1.1 (s.queued.erase root.1.1) k.1 := by
  unfold hsearch_lazy_pushKeys at hk
  rcases List.mem_append.mp hk with h | h
  · unfold hsearch_lazy_changedKeys at h
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp h
    have hq' := (hsearch_lazy_changedSorted_perm G heur s root.1.1
      (s.queued.erase root.1.1)).subset hq
    obtain ⟨x, hx, n, -, -, rfl⟩ := (hsearch_lazy_mem_changedPairs_iff G heur s root.1.1
      (s.queued.erase root.1.1) q).mp hq'
    exact hsearch_lazy_items_order G heur s root T hp hlive hT x hx
  · unfold hsearch_lazy_newlyKeys at h
    obtain ⟨x, hx, hxk⟩ := List.mem_filterMap.mp h
    by_cases hnew : x.2.2.2
    · rw [if_pos hnew] at hxk
      obtain rfl := (Option.some.inj hxk).symm
      exact hsearch_lazy_items_order G heur s root T hp hlive hT x hx
    · rw [if_neg hnew] at hxk
      exact absurd hxk (by simp)

/-- A live entry of the new heap carries the new path order of its vertex. -/
theorem hsearch_lazy_newHeap_live_key :
    ∀ e ∈ (hsearch_lazy_newHeap G heur s root.1.1 (s.queued.erase root.1.1)).elems,
      hsearch_lazy_isLive
          (hsearch_lazy_newQueued G heur s root.1.1 (s.queued.erase root.1.1)) e = true →
        e.1.2 = hsearch_lazy_new_order G heur s root.1.1 (s.queued.erase root.1.1) e.1.1 := by
  intro e he hl
  rcases List.mem_append.mp ((hsearch_lazy_newHeap_perm G heur s root T hp hT
      (s.queued.erase root.1.1)).mem_iff.mp he) with h | h
  · rw [hsearch_lazy_isLive_new G heur s root T hlive hT e h, Bool.and_eq_true] at hl
    have hc : hsearch_lazy_isChanged G heur s root.1.1 (s.queued.erase root.1.1) e = false := by
      simpa using hl.2
    have hrep := hsearch_lazy_replace_eq_self G heur s root T hp hlive hT e h hl.1 hc
    exact (congrArg (fun z : LazyEntry V => z.1.2) hrep).symm
  · have hk : e.1 ∈ hsearch_lazy_pushKeys G heur s root.1.1 (s.queued.erase root.1.1) := by
      have hm : e.1 ∈ (hsearch_lazy_pushEntries G heur s root.1.1
          (s.queued.erase root.1.1)).map Prod.fst := List.mem_map_of_mem h
      rwa [hsearch_lazy_pushEntries, List.zipIdx_map_fst] at hm
    exact hsearch_lazy_pushKeys_order G heur s root T hp hlive hT e.1 hk

/-- Every vertex queued after the expansion has its live entry in the new heap. -/
theorem hsearch_lazy_newHeap_queued_live (v : V) (n : ℕ)
    (hv : (hsearch_lazy_newQueued G heur s root.1.1 (s.queued.erase root.1.1))[v]? = some n) :
    ∃ e ∈ (hsearch_lazy_newHeap G heur s root.1.1 (s.queued.erase root.1.1)).elems,
      e.1.1 = v ∧ e.2 = n := by
  by_cases hpush : v ∈
      (hsearch_lazy_pushKeys G heur s root.1.1 (s.queued.erase root.1.1)).map Prod.fst
  · rw [← hsearch_lazy_pushEntries_map] at hpush
    obtain ⟨e, he, hev⟩ := List.mem_map.mp hpush
    have hvv := hsearch_lazy_newQueued_pushed G heur s root.1.1
      (s.queued.erase root.1.1) rfl e he
    rw [hev, hv] at hvv
    exact ⟨e, (hsearch_lazy_newHeap_perm G heur s root T hp hT
      (s.queued.erase root.1.1)).mem_iff.mpr (List.mem_append_right _ he), hev,
      (Option.some.inj hvv).symm⟩
  · rw [hsearch_lazy_newQueued_not_pushed G heur s root.1.1
      (s.queued.erase root.1.1) v hpush] at hv
    have hne : ¬ (root.1.1 = v) := by
      intro h
      rw [Std.HashMap.getElem?_erase, if_pos (by simpa using h)] at hv
      simp at hv
    have hq : s.queued[v]? = some n := by
      rwa [Std.HashMap.getElem?_erase, if_neg (by simpa using hne)] at hv
    obtain ⟨e, hem, hev, hen⟩ := s.queued_live v n hq
    have hmemT : e ∈ T := by
      have hmem : e ∈ root :: T := by
        rw [← hT]; exact (hsearch_lazy_sorted_perm heur s).mem_iff.mpr hem
      rcases List.mem_cons.mp hmem with rfl | h
      · exact absurd hev hne
      · exact h
    exact ⟨e, (hsearch_lazy_newHeap_perm G heur s root T hp hT
      (s.queued.erase root.1.1)).mem_iff.mpr (List.mem_append_left _ hmemT), hev, hen⟩

omit hp hlive hT in
/-- Only visited vertices are queued after the expansion. -/
theorem hsearch_lazy_newQueued_visited (v : V)
    (hc : (hsearch_lazy_newQueued G heur s root.1.1
      (s.queued.erase root.1.1)).contains v = true) :
    v ∈ (s.vis.insertList (hsearch_lazy_newly G heur s root.1.1
      (s.queued.erase root.1.1))).toFinset := by
  rw [VisitedSet.insertList_toFinset]
  rw [hsearch_lazy_newQueued, Std.HashMap.contains_foldl_insert] at hc
  have hqv : ∀ w : V, (s.queued.erase root.1.1).contains w = true →
      w ∈ s.vis.toFinset := by
    intro w hw
    rw [Std.HashMap.contains_erase, Bool.and_eq_true] at hw
    exact s.queued_visited w hw.2
  rcases hc with h | h
  · rw [hsearch_lazy_pushEntries_map, hsearch_lazy_pushKeys_map] at h
    rcases List.mem_append.mp h with h1 | h1
    · exact Finset.mem_union_left _ (hqv v (hsearch_lazy_changed_qt G heur s root.1.1
        (s.queued.erase root.1.1) v h1))
    · exact Finset.mem_union_right _ (List.mem_toFinset.mpr h1)
  · exact Finset.mem_union_left _ (hqv v h)

/-!
### The queue after the expansion
-/

/-- The live entries of the new heap are exactly `hsearch_lazy_D_ref`. -/
theorem hsearch_lazy_filter_D_ref :
    (hsearch_lazy_D_ref G heur s root T
        ++ T.filter (fun e => !hsearch_lazy_isLive
          (hsearch_lazy_newQueued G heur s root.1.1 (s.queued.erase root.1.1)) e)).filter
      (hsearch_lazy_isLive (hsearch_lazy_newQueued G heur s root.1.1 (s.queued.erase root.1.1)))
      = hsearch_lazy_D_ref G heur s root T := by
  rw [List.filter_append,
    List.filter_eq_self.mpr (hsearch_lazy_D_ref_live G heur s root T hp hlive hT)]
  have hnil : (T.filter (fun e => !hsearch_lazy_isLive
        (hsearch_lazy_newQueued G heur s root.1.1 (s.queued.erase root.1.1)) e)).filter
      (hsearch_lazy_isLive
        (hsearch_lazy_newQueued G heur s root.1.1 (s.queued.erase root.1.1))) = [] := by
    rw [List.filter_filter]
    refine List.filter_eq_nil_iff.mpr ?_
    intro a _
    simp
  rw [hnil, List.append_nil]

/-- **The queue after one expansion is the queue of the reference implementation**: the
stale entries left in the heap are invisible, and the fresh numbers of the re-inserted nodes
reproduce the tie-breaking of the stable sort. -/
theorem hsearch_lazy_newHeap_liveQueue :
    (HeapQueue.liveQueue (hsearch_lazy_key_le heur)
        (hsearch_lazy_isLive (hsearch_lazy_newQueued G heur s root.1.1 (s.queued.erase root.1.1)))
        (hsearch_lazy_newHeap G heur s root.1.1 (s.queued.erase root.1.1))).map Prod.fst
      = (hsearch_lazy_tail heur s T
          ++ hsearch_lazy_newly G heur s root.1.1 (s.queued.erase root.1.1)).mergeSort
          (hsearch_queue_le heur
            (hsearch_lazy_new_order G heur s root.1.1 (s.queued.erase root.1.1))) := by
  have hperm := hsearch_lazy_D_ref_perm G heur s root T hp hlive hT
  have hfil := hsearch_lazy_filter_D_ref G heur s root T hp hlive hT
  have hnd := ((hperm.map Prod.snd).nodup_iff).mp
    (hsearch_lazy_newHeap_nodup G heur s root T hp hT (s.queued.erase root.1.1))
  have h1 := HeapQueue.liveQueue_eq (hsearch_lazy_key_le heur) (hsearch_lazy_key_le_trans heur)
    (hsearch_lazy_key_le_total heur) _ _ _ hperm hnd
    (by rw [hfil]; exact hsearch_lazy_D_ref_tie G heur s root T hp hlive hT)
  rw [h1, hfil, ← hsearch_lazy_D_ref_map G heur s root T,
    show ((hsearch_lazy_D_ref G heur s root T).map (fun e => e.1.1))
      = (((hsearch_lazy_D_ref G heur s root T).map Prod.fst).map Prod.fst) by
      simp [List.map_map, Function.comp_def]]
  refine List.map_mergeSort ?_
  intro a ha b hb
  have hkey : ∀ c ∈ (hsearch_lazy_D_ref G heur s root T).map Prod.fst,
      c.2 = hsearch_lazy_new_order G heur s root.1.1 (s.queued.erase root.1.1) c.1 := by
    intro c hc
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hc
    refine hsearch_lazy_newHeap_live_key G heur s root T hp hlive hT e ?_
      (hsearch_lazy_D_ref_live G heur s root T hp hlive hT e he)
    exact hperm.mem_iff.mpr (List.mem_append_left _ he)
  have ha' : a = (a.1, hsearch_lazy_new_order G heur s root.1.1
    (s.queued.erase root.1.1) a.1) := Prod.ext rfl (hkey a ha)
  have hb' : b = (b.1, hsearch_lazy_new_order G heur s root.1.1
    (s.queued.erase root.1.1) b.1) := Prod.ext rfl (hkey b hb)
  calc hsearch_lazy_key_le heur a b
      = hsearch_lazy_key_le heur
          (a.1, hsearch_lazy_new_order G heur s root.1.1 (s.queued.erase root.1.1) a.1)
          (b.1, hsearch_lazy_new_order G heur s root.1.1 (s.queued.erase root.1.1) b.1) := by
        rw [← ha', ← hb']
    _ = hsearch_queue_le heur
          (hsearch_lazy_new_order G heur s root.1.1 (s.queued.erase root.1.1)) a.1 b.1 := rfl


end

end NatGraph
