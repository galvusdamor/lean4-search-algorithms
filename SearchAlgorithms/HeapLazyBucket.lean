import SearchAlgorithms.HeapLazyStored
import SearchAlgorithms.BucketQueue
import SearchAlgorithms.SearchSimRel

/-!
# The search with stored `f`-values on a bucket queue

`astar_heap_stored_fastpath` keeps its queue in a leftist heap, ordered by the stored key
(`f`-value and tie-breaker) and the insertion number.  Insertion numbers increase, so a
**bucket queue** — one FIFO bucket per key, the buckets sorted by key
(`SearchAlgorithms.BucketQueue`) — pops the entries in the same order, without the walks along
the spines of the heap.

The state of this search (`hsearch_bq_state`) is the data of a stored state with the heap
replaced by a bucket queue, together with the proof that it is **related** to a stored state
(`BQRel`): same fields, and the entries of the bucket queue are the sorted list of the heap
(`HeapQueue.sortedList`).  Since the order is total and the insertion numbers are distinct,
that list does not depend on the shape of the heap, and purging, popping and inserting act on
it in the same way on both sides.  Every step therefore preserves the relation, the abstract
states agree, and the search returns the same path as `astar_heap_stored_fastpath`
(`astar_bq_fastpath_eq_stored`, installed with `@[csimp]`).
-/

namespace NatGraph

open WeightedDiGraph
open SearchAlgorithms

variable {V : Type} [FinEnum V] [BEq V] [LawfulBEq V] [Hashable V]

/-! ### The order -/

/-- The key of an entry in the bucket queue: its stored value. -/
@[inline] def bkey (e : StoredEntry V) : ℕ × ℕ := e.1.2

/-- The insertion number of an entry. -/
@[inline] def bidx (e : StoredEntry V) : ℕ := e.2

omit [FinEnum V] [BEq V] [LawfulBEq V] [Hashable V] in
theorem storedKeyLe_trans : ∀ a b c : StoredKey V,
    storedKeyLe a b → storedKeyLe b c → storedKeyLe a c := by
  intro a b c h1 h2
  obtain ⟨_, a1, a2⟩ := a
  obtain ⟨_, b1, b2⟩ := b
  obtain ⟨_, c1, c2⟩ := c
  simp only [storedKeyLe, FValueComp.lt, Nat.FValueLT, Prod.lex_def, Prod.mk.injEq,
    Bool.or_eq_true, decide_eq_true_eq] at *
  omega

omit [FinEnum V] [BEq V] [LawfulBEq V] [Hashable V] in
theorem storedKeyLe_total : ∀ a b : StoredKey V, (storedKeyLe a b || storedKeyLe b a) = true := by
  intro a b
  obtain ⟨_, a1, a2⟩ := a
  obtain ⟨_, b1, b2⟩ := b
  simp only [storedKeyLe, FValueComp.lt, Nat.FValueLT, Prod.lex_def, Prod.mk.injEq,
    Bool.or_eq_true, decide_eq_true_eq]
  omega

omit [FinEnum V] [BEq V] [LawfulBEq V] [Hashable V] in
theorem zipIdxLE_of_bq {x y : StoredEntry V}
    (h : keyLt (bkey x) (bkey y) = true ∨ (bkey x = bkey y ∧ bidx x < bidx y)) :
    List.zipIdxLE storedKeyLe x y = true := by
  show storedLe x y = true
  rw [storedLe_eq_fast]
  obtain ⟨⟨_, x1, x2⟩, i⟩ := x
  obtain ⟨⟨_, y1, y2⟩, j⟩ := y
  simp only [bkey, bidx, keyLt_iff, Prod.mk.injEq] at h
  simp only [storedLeFast, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
  omega

omit [FinEnum V] [BEq V] [LawfulBEq V] [Hashable V] in
/-- **The entries of a well-formed bucket queue are the sorted list of any heap with the same
entries.** -/
theorem bq_eq_sortedList (q : RQ (StoredEntry V)) (h : LHeap (StoredEntry V))
    (hwf : RQ.WF bkey bidx q) (hperm : (RQ.elems q).Perm h.elems)
    (hnd : (h.elems.map Prod.snd).Nodup) :
    RQ.elems q = HeapQueue.sortedList storedKeyLe h := by
  refine SortAux.eq_of_perm_of_zipIdxLE storedKeyLe _ _
    (hperm.trans (HeapQueue.sortedList_perm storedKeyLe h).symm)
    ((RQ.sorted_elems hwf).imp (fun hxy => zipIdxLE_of_bq hxy))
    (HeapQueue.sortedList_pairwise storedKeyLe storedKeyLe_trans storedKeyLe_total h) ?_
  exact ((hperm.map Prod.snd).nodup_iff).mpr hnd

/-! ### Facts about the stored state -/

section

variable {heur : V → ℕ∞}

omit [LawfulBEq V] in
theorem stored_ordered (s : hsearch_stored_state V heur) :
    LHeap.Ordered (List.zipIdxLE storedKeyLe) s.heap :=
  LHeap.Ordered_of_map storedLe (hsearch_lazy_le heur) eraseEntry s.heap
    (storedLe_agree heur _ s.heap_keys) s.heap_ordered

omit [LawfulBEq V] in
theorem stored_nodup (s : hsearch_stored_state V heur) : (s.heap.elems.map Prod.snd).Nodup := by
  have := s.seq_nodup
  simpa [LHeap.elems_map, List.map_map, Function.comp_def, HeapQueue.entryMap] using this

omit [LawfulBEq V] in
theorem stored_seq_lt (s : hsearch_stored_state V heur) : ∀ e ∈ s.heap.elems, e.2 < s.nextSeq := by
  intro e he
  have := s.seq_lt (eraseEntry e) (by
    rw [LHeap.elems_map]; exact List.mem_map_of_mem he)
  simpa [HeapQueue.entryMap] using this

omit [LawfulBEq V] in
/-- The root of the stored heap is the head of its sorted list. -/
theorem stored_peek_eq (s : hsearch_stored_state V heur) :
    s.heap.peek = (HeapQueue.sortedList storedKeyLe s.heap).head? := by
  cases hp : s.heap.peek with
  | none =>
    have he : s.heap.elems = [] := (LHeap.peek_eq_none_iff _).mp hp
    have : HeapQueue.sortedList storedKeyLe s.heap = [] := by
      have := HeapQueue.sortedList_perm storedKeyLe s.heap
      rw [he] at this
      exact this.eq_nil
    rw [this]; rfl
  | some x =>
    obtain ⟨t, ht⟩ := HeapQueue.sortedList_head storedKeyLe storedKeyLe_trans storedKeyLe_total
      s.heap x (stored_ordered s) (stored_nodup s) hp
    rw [ht]; rfl

end

/-! ### Purging -/

/-- Drop the stale entries at the front of a bucket queue. -/
def purgeQ (p : StoredEntry V → Bool) (q : RQ (StoredEntry V)) : RQ (StoredEntry V) :=
  match hq : q.peek with
  | none => q
  | some x =>
    if p x then q
    else
      have _h : RQ.msize (RQ.pop q) < RQ.msize q := RQ.msize_pop_lt q x hq
      purgeQ p (RQ.pop q)
termination_by RQ.msize q

omit [FinEnum V] [BEq V] [LawfulBEq V] [Hashable V] in
theorem purgeQ_none (p : StoredEntry V → Bool) (q : RQ (StoredEntry V)) (hq : q.peek = none) :
    purgeQ p q = q := by
  rw [purgeQ]; split <;> simp_all

omit [FinEnum V] [BEq V] [LawfulBEq V] [Hashable V] in
theorem purgeQ_live (p : StoredEntry V → Bool) (q : RQ (StoredEntry V)) (x : StoredEntry V)
    (hq : q.peek = some x) (hx : p x = true) : purgeQ p q = q := by
  rw [purgeQ]; split <;> simp_all

omit [FinEnum V] [BEq V] [LawfulBEq V] [Hashable V] in
theorem purgeQ_stale (p : StoredEntry V → Bool) (q : RQ (StoredEntry V)) (x : StoredEntry V)
    (hq : q.peek = some x) (hx : ¬ p x = true) : purgeQ p q = purgeQ p (RQ.pop q) := by
  rw [purgeQ]; split <;> simp_all

omit [FinEnum V] [BEq V] [LawfulBEq V] [Hashable V] in
theorem purgeQ_spec (p : StoredEntry V → Bool) :
    ∀ (q : RQ (StoredEntry V)), RQ.WF bkey bidx q →
      RQ.WF bkey bidx (purgeQ p q) ∧
        RQ.elems (purgeQ p q) = (RQ.elems q).dropWhile (fun x => !p x) := by
  intro q
  induction q using purgeQ.induct p with
  | case1 q hq =>
    intro hwf
    rw [purgeQ_none p q hq]
    refine ⟨hwf, ?_⟩
    rw [RQ.peek_eq hwf, List.head?_eq_none_iff] at hq
    rw [hq]; rfl
  | case2 q x hq hx =>
    intro hwf
    rw [purgeQ_live p q x hq hx]
    refine ⟨hwf, ?_⟩
    rw [RQ.peek_eq hwf] at hq
    cases he : RQ.elems q with
    | nil => rw [he] at hq; cases hq
    | cons y t =>
      rw [he] at hq
      cases hq
      simp [hx]
  | case3 q x hq hx _ ih =>
    intro hwf
    rw [purgeQ_stale p q x hq hx]
    obtain ⟨h1, h2⟩ := ih (RQ.WF_pop hwf)
    refine ⟨h1, ?_⟩
    rw [h2, RQ.elems_pop hwf]
    rw [RQ.peek_eq hwf] at hq
    cases he : RQ.elems q with
    | nil => rw [he] at hq; cases hq
    | cons y t =>
      rw [he] at hq
      cases hq
      simp [hx]

omit [FinEnum V] [BEq V] [LawfulBEq V] [Hashable V] in
/-- **Purging the heap drops the stale entries at the front of its sorted list.** -/
theorem sortedList_purge (p : StoredEntry V → Bool) :
    ∀ (h : LHeap (StoredEntry V)), LHeap.Ordered (List.zipIdxLE storedKeyLe) h →
      (h.elems.map Prod.snd).Nodup →
      HeapQueue.sortedList storedKeyLe (HeapQueue.purge storedKeyLe p h)
        = (HeapQueue.sortedList storedKeyLe h).dropWhile (fun x => !p x) := by
  intro h
  induction h using HeapQueue.purge.induct storedKeyLe p with
  | case1 h hpk =>
    intro _ _
    have hp : HeapQueue.purge storedKeyLe p h = h := by
      rw [HeapQueue.purge.eq_def]; split <;> simp_all
    rw [hp]
    have he : h.elems = [] := (LHeap.peek_eq_none_iff _).mp hpk
    have : HeapQueue.sortedList storedKeyLe h = [] := by
      have := HeapQueue.sortedList_perm storedKeyLe h
      rw [he] at this
      exact this.eq_nil
    rw [this]; rfl
  | case2 h x hpk hx =>
    intro hord hnd
    have hp : HeapQueue.purge storedKeyLe p h = h := by
      rw [HeapQueue.purge.eq_def]; split <;> simp_all
    rw [hp]
    obtain ⟨t, ht⟩ := HeapQueue.sortedList_head storedKeyLe storedKeyLe_trans storedKeyLe_total
      h x hord hnd hpk
    rw [ht]
    simp [hx]
  | case3 h x hpk hx _ ih =>
    intro hord hnd
    have hp : HeapQueue.purge storedKeyLe p h
        = HeapQueue.purge storedKeyLe p (LHeap.deleteMin (List.zipIdxLE storedKeyLe) h) := by
      rw [HeapQueue.purge.eq_def]; split <;> simp_all
    rw [hp]
    have hord' := LHeap.Ordered_deleteMin _ (List.zipIdxLE_total (le := storedKeyLe) storedKeyLe_total)
      (List.zipIdxLE_trans (le := storedKeyLe) storedKeyLe_trans) h hord
    have hnd' : ((LHeap.deleteMin (List.zipIdxLE storedKeyLe) h).elems.map Prod.snd).Nodup := by
      have h1 := LHeap.elems_deleteMin (List.zipIdxLE storedKeyLe) h x hpk
      have := ((h1.map Prod.snd).nodup_iff).mp hnd
      rw [List.map_cons] at this
      exact this.of_cons
    rw [ih hord' hnd', HeapQueue.sortedList_deleteMin storedKeyLe storedKeyLe_trans
      storedKeyLe_total h hord hnd]
    obtain ⟨t, ht⟩ := HeapQueue.sortedList_head storedKeyLe storedKeyLe_trans storedKeyLe_total
      h x hord hnd hpk
    rw [ht]
    simp [hx]

/-! ### The state -/

/-- The data of a state of the bucket queue search: that of `hsearch_stored_state`, with a
bucket queue instead of the heap. -/
structure hsearch_bq_data (V : Type) [BEq V] [Hashable V] [FinEnum V] (heur : V → ℕ∞) where
  vis : VisitedSet V
  orderMap : Std.HashMap V (ℕ × ℕ)
  orderDefault : ℕ × ℕ
  motherMap : Std.HashMap V V
  motherDefault : V
  queue : RQ (StoredEntry V)
  queued : Std.HashMap V ℕ
  nextSeq : ℕ
  expansions : ℕ
  traceEvery : ℕ

variable {heur : V → ℕ∞}

/-- The data of a stored state with the given bucket queue. -/
def ofStored (s : hsearch_stored_state V heur) (q : RQ (StoredEntry V)) :
    hsearch_bq_data V heur :=
  ⟨s.vis, s.orderMap, s.orderDefault, s.motherMap, s.motherDefault, q, s.queued, s.nextSeq,
    s.expansions, s.traceEvery⟩

/-- **The relation to a stored state**: the same data, and the entries of the bucket queue
are the sorted list of the heap. -/
def BQRel (d : hsearch_bq_data V heur) (s : hsearch_stored_state V heur) : Prop :=
  ∃ q, d = ofStored s q ∧ RQ.WF bkey bidx q ∧ RQ.elems q = HeapQueue.sortedList storedKeyLe s.heap

/-- **A state of the bucket queue search**: data related to a stored state. -/
def hsearch_bq_state (V : Type) [BEq V] [LawfulBEq V] [Hashable V] [FinEnum V]
    (heur : V → ℕ∞) : Type :=
  {d : hsearch_bq_data V heur // ∃ s, BQRel d s}

/-! ### Purging -/

/-- Drop the stale entries at the front of the queue. -/
def bqPurge (d : hsearch_bq_data V heur) : hsearch_bq_data V heur :=
  { d with queue := purgeQ (storedIsLive d.queued) d.queue }

omit [LawfulBEq V] in
theorem bqPurge_rel {d : hsearch_bq_data V heur} {s : hsearch_stored_state V heur}
    (h : BQRel d s) : BQRel (bqPurge d) (hsearch_stored_purgeState heur s) := by
  obtain ⟨q, rfl, hwf, he⟩ := h
  obtain ⟨h1, h2⟩ := purgeQ_spec (storedIsLive s.queued) q hwf
  refine ⟨_, rfl, h1, ?_⟩
  show RQ.elems (purgeQ (storedIsLive s.queued) q) = HeapQueue.sortedList storedKeyLe
    (HeapQueue.purge storedKeyLe (storedIsLive s.queued) s.heap)
  rw [h2, he, sortedList_purge _ s.heap (stored_ordered s) (stored_nodup s)]

omit [LawfulBEq V] in
/-- Related states have the same root. -/
theorem bq_peek_eq {d : hsearch_bq_data V heur} {s : hsearch_stored_state V heur}
    (h : BQRel d s) : d.queue.peek = s.heap.peek := by
  obtain ⟨q, rfl, hwf, he⟩ := h
  show q.peek = _
  rw [RQ.peek_eq hwf, he, stored_peek_eq]

/-! ### One expansion -/

theorem mem_zipIdx_ge {α : Type} : ∀ (l : List α) (n : ℕ) (y : α × ℕ), y ∈ l.zipIdx n → n ≤ y.2
  | [], _, _, h => by cases h
  | a :: l, n, y, h => by
    rw [List.zipIdx_cons, List.mem_cons] at h
    rcases h with rfl | h
    · exact le_refl _
    · exact Nat.le_of_succ_le (mem_zipIdx_ge l (n + 1) y h)

theorem pairwise_zipIdx {α : Type} : ∀ (l : List α) (n : ℕ),
    (l.zipIdx n).Pairwise (fun x y => x.2 < y.2)
  | [], _ => List.Pairwise.nil
  | a :: l, n => by
    rw [List.zipIdx_cons, List.pairwise_cons]
    exact ⟨fun y hy => Nat.lt_of_succ_le (mem_zipIdx_ge l (n + 1) y hy), pairwise_zipIdx l (n + 1)⟩


section

variable (G : NatGraphWithGenerator V) (heur : V → ℕ∞)

/-- **One expansion on the bucket queue**: `hsearch_stored_core` with the heap operations
replaced by the bucket queue ones. -/
def bqCore (d : hsearch_bq_data V heur) (root : StoredEntry V) : hsearch_bq_data V heur :=
  let head : V := root.1.1.1
  let vis0 := d.vis
  let om := d.orderMap
  let od := d.orderDefault
  let mm := d.motherMap
  let md := d.motherDefault
  let heap0 := d.queue
  let q0 := d.queued
  let ns := d.nextSeq
  let ex := d.expansions
  let te := d.traceEvery
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
  let newHeap : RQ (StoredEntry V) := RQ.insertAll bkey (RQ.pop heap0) pushEntries
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
    queue := newHeap
    queued := newQueued
    nextSeq := ns + pushEntries.length
    expansions := ex + 1
    traceEvery := te
 }

theorem stored_core_heap (s : hsearch_stored_state V heur) (root : StoredEntry V)
    (hp : s.heap.peek = some root)
    (hlive : hsearch_lazy_isLive s.queued (eraseEntry root) = true) :
    (hsearch_stored_core G heur s root hp hlive).heap
      = hsearch_stored_newHeap G heur s root.1.1.1 (s.queued.erase root.1.1.1) := by
  unfold hsearch_stored_core
  simp only [traceIf_eq]
  rfl

/-- **One expansion preserves the relation.** -/
theorem bqCore_rel {d : hsearch_bq_data V heur} {s : hsearch_stored_state V heur}
    (h : BQRel d s) (root : StoredEntry V) (hp : s.heap.peek = some root)
    (hlive : hsearch_lazy_isLive s.queued (eraseEntry root) = true) :
    BQRel (bqCore G heur d root) (hsearch_stored_core G heur s root hp hlive) := by
  obtain ⟨q, rfl, hwf, he⟩ := h
  let push := hsearch_stored_pushEntries G heur s root.1.1.1 (s.queued.erase root.1.1.1)
  have hlt : ∀ x ∈ RQ.elems (RQ.pop q), ∀ y ∈ push, bidx x < bidx y := by
    intro x hx y hy
    rw [RQ.elems_pop hwf] at hx
    have hx' : x ∈ s.heap.elems := by
      have := List.mem_of_mem_tail hx
      rw [he] at this
      exact (HeapQueue.sortedList_perm storedKeyLe s.heap).mem_iff.mp this
    exact Nat.lt_of_lt_of_le (stored_seq_lt s x hx') (mem_zipIdx_ge _ _ y hy)
  obtain ⟨hperm, hwf'⟩ := RQ.elems_insertAll_WF push (RQ.pop q) (RQ.WF_pop hwf) hlt
    (pairwise_zipIdx _ _)
  refine ⟨RQ.insertAll bkey (RQ.pop q) push, ?_, hwf', ?_⟩
  · unfold bqCore hsearch_stored_core ofStored
    simp only [traceIf_eq]
    rfl
  · rw [stored_core_heap]
    obtain ⟨t, ht⟩ := HeapQueue.sortedList_head storedKeyLe storedKeyLe_trans storedKeyLe_total
      s.heap root (stored_ordered s) (stored_nodup s) hp
    have hdel : (LHeap.deleteMin storedLe s.heap).elems.Perm t := by
      have h1 := LHeap.elems_deleteMin storedLe s.heap root hp
      have h2 : s.heap.elems.Perm (root :: t) :=
        (HeapQueue.sortedList_perm storedKeyLe s.heap).symm.trans (by rw [ht])
      exact List.Perm.cons_inv (h1.symm.trans h2)
    refine bq_eq_sortedList _ _ hwf' ?_ ?_
    · refine hperm.trans ?_
      rw [RQ.elems_pop hwf, he, ht, List.tail_cons]
      refine List.Perm.trans ?_ (LHeap.elems_insertAll storedLe _ _).symm
      exact hdel.symm.append_right _
    · have := stored_nodup (hsearch_stored_core G heur s root hp hlive)
      rwa [stored_core_heap] at this

/-- **One expansion step on the bucket queue**: purge, then expand the root. -/
def bqExpand (d : hsearch_bq_data V heur) : hsearch_bq_data V heur :=
  match (bqPurge d).queue.peek with
  | none => bqPurge d
  | some root => bqCore G heur (bqPurge d) root

theorem bqExpand_rel {d : hsearch_bq_data V heur} {s : hsearch_stored_state V heur}
    (h : BQRel d s) (head : V) (tail : List V) :
    BQRel (bqExpand G heur d) (hsearch_step_expand_stored G heur s head tail) := by
  have hpr := bqPurge_rel h
  have hpk := bq_peek_eq hpr
  unfold bqExpand hsearch_step_expand_stored
  cases hq : (bqPurge d).queue.peek with
  | none =>
    have hs : (hsearch_stored_purgeState heur s).heap.peek = none := by rw [← hpk, hq]
    dsimp only
    split
    · exact hpr
    · rename_i r hr; rw [hs] at hr; cases hr
  | some root =>
    have hs : (hsearch_stored_purgeState heur s).heap.peek = some root := by rw [← hpk, hq]
    dsimp only
    split
    · rename_i hr; rw [hs] at hr; cases hr
    · rename_i r hr
      rw [hs] at hr
      cases hr
      exact bqCore_rel G heur hpr root _ _

end

/-! ### The abstract state -/

section

variable {heur : V → ℕ∞}

/-- The abstract state of the data of a bucket queue state. -/
@[reducible]
def bqToBase {g : NatGraph V} (d : hsearch_bq_data V heur) : hsearch_search_state g where
  visited := d.vis.toFinset
  pathOrder := fun v => d.orderMap.getD v d.orderDefault
  mother := fun x => d.motherMap.getD x.1 d.motherDefault
  stack := ((RQ.elems d.queue).filter (storedIsLive d.queued)).map (fun e => e.1.1.1)

omit [LawfulBEq V] in
theorem bqToBase_eq {g : NatGraph V} {d : hsearch_bq_data V heur} {s : hsearch_stored_state V heur}
    (h : BQRel d s) : bqToBase (g := g) d = s.toBaseState := by
  obtain ⟨q, rfl, -, he⟩ := h
  unfold bqToBase hsearch_stored_state.toBaseState hsearch_stored_state.storedQueue
  simp only [ofStored]
  rw [he]

instance instHasBaseSearchStateBQ (g : NatGraph V) (heur : V → ℕ∞) :
    WeightedDiGraph.has_base_search_state g (ℕ × ℕ) (hsearch_bq_state V heur) where
  to_base_state := fun s => bqToBase s.1

theorem bq_to_base {g : NatGraph V} (s : hsearch_bq_state V heur) {st : hsearch_stored_state V heur}
    (h : BQRel s.1 st) :
    has_base_search_state.to_base_state (G := g) (D := ℕ × ℕ) s
      = has_base_search_state.to_base_state (G := g) (D := ℕ × ℕ) st :=
  bqToBase_eq h

end

/-! ### The search -/

section

variable (G : NatGraphWithGenerator V) (heur : V → ℕ∞)

/-- One expansion step on bucket queue states. -/
def hsearch_step_expand_bq (s : hsearch_bq_state V heur) (_head : V) (_tail : List V) :
    hsearch_bq_state V heur :=
  ⟨bqExpand G heur s.1, by
    obtain ⟨st, h⟩ := s.2
    exact ⟨_, bqExpand_rel G heur h _head _tail⟩⟩

/-- The expansion of a state whose purged queue has the root `root`: `bqCore` on the purged
data (it is `hsearch_step_expand_bq`, `expand_bq_of_root`). -/
def hsearch_expand_bq_root (s : hsearch_bq_state V heur) (root : StoredEntry V)
    (hq : (bqPurge s.1).queue.peek = some root) : hsearch_bq_state V heur :=
  ⟨bqCore G heur (bqPurge s.1) root, by
    obtain ⟨st, h⟩ := s.2
    have := bqExpand_rel G heur h root.1.1.1 []
    unfold bqExpand at this
    rw [hq] at this
    exact ⟨_, this⟩⟩

theorem expand_bq_of_root (s : hsearch_bq_state V heur) (root : StoredEntry V)
    (hq : (bqPurge s.1).queue.peek = some root) (head : V) (tail : List V) :
    hsearch_expand_bq_root G heur s root hq = hsearch_step_expand_bq G heur s head tail := by
  apply Subtype.ext
  show bqCore G heur (bqPurge s.1) root = bqExpand G heur s.1
  unfold bqExpand
  rw [hq]

/-- **The step function of the bucket queue search**: the next node is read off the queue. -/
def hsearch_bq_step :
    search_step_function (G.toWeightedDiGraph) (ℕ × ℕ) (hsearch_bq_state V heur) :=
  fun goal s =>
    match hq : (bqPurge s.1).queue.peek with
    | none => (s, some false)
    | some root =>
      if root.1.1.1 = goal then (s, some true)
      else (hsearch_expand_bq_root G heur s root hq, none)

theorem hsearch_bq_step_eq :
    hsearch_bq_step G heur
      = search_stack_step (G := G.toWeightedDiGraph) (D := ℕ × ℕ)
          (state_type := hsearch_bq_state V heur) (hsearch_step_expand_bq G heur) := by
  funext goal s
  obtain ⟨st, h⟩ := s.2
  have hpk := bq_peek_eq (bqPurge_rel h)
  unfold hsearch_bq_step search_stack_step
  show _ = (match (bqToBase (g := G.toWeightedDiGraph) s.1).stack with
    | [] => (s, some false)
    | x :: t => if x = goal then (s, some true)
        else (hsearch_step_expand_bq G heur s x t, none))
  have hst : (st.toBaseState (g := G.toWeightedDiGraph)).stack = st.erase.queue :=
    hsearch_stored_state.storedQueue_eq st
  rw [bqToBase_eq h, hst]
  split
  · next hq =>
    rw [stored_queue_nil heur st (by rw [← hpk, hq])]
  · next root hq =>
    rw [stored_queue_cons heur st root (by rw [← hpk, hq])]
    simp only
    split
    · rfl
    · rw [expand_bq_of_root G heur s root hq]

/-- The termination metric: that of the abstract state. -/
def hsearch_bq_termination_metric (s : hsearch_bq_state V heur) : ℕ × ℕ × ℕ × ℕ :=
  hsearch_termination_metric_nat (bqToBase (g := G.toWeightedDiGraph) s.1)

theorem hsearch_bq_metric_eq (s : hsearch_bq_state V heur) {st : hsearch_stored_state V heur}
    (h : BQRel s.1 st) :
    hsearch_bq_termination_metric G heur s = hsearch_stored_termination_metric G heur st := by
  unfold hsearch_bq_termination_metric hsearch_stored_termination_metric
    hsearch_lazy_termination_metric
  rw [bqToBase_eq h, hsearch_stored_state.toBaseState_eq]

theorem hsearch_bq_expand_metric_reduction (goal : V) :
    WeightedDiGraph.termination_proof_for_expand (G := G.toWeightedDiGraph) (D := ℕ × ℕ)
      (state_type := hsearch_bq_state V heur) (hsearch_step_expand_bq G heur) goal
      (hsearch_bq_termination_metric G heur) := by
  intro s head tail hs
  obtain ⟨st, h⟩ := s.2
  have h' := bqExpand_rel G heur h head tail
  have := hsearch_stored_expand_metric_reduction G heur goal st head tail
    (by rw [← bq_to_base s h]; exact hs)
  rw [hsearch_bq_metric_eq G heur s h,
    hsearch_bq_metric_eq G heur (hsearch_step_expand_bq G heur s head tail) h']
  exact this

theorem hsearch_bq_expand_keeps_base_invars (start goal : V) :
    WeightedDiGraph.base_invar_carries_over_expand (G := G.toWeightedDiGraph) (D := ℕ × ℕ)
      (state_type := hsearch_bq_state V heur) (hsearch_step_expand_bq G heur) goal
      (WeightedDiGraph.search_invar_all_basic (G := G.toWeightedDiGraph) (D := ℕ × ℕ)
        (hsearch_expandable heur) start) := by
  intro s head tail hs
  obtain ⟨st, h⟩ := s.2
  have h' := bqExpand_rel G heur h head tail
  have := hsearch_stored_expand_keeps_base_invars G heur start goal st head tail
    (by rw [← bq_to_base s h]; exact hs)
  rw [bq_to_base (hsearch_step_expand_bq G heur s head tail) h']
  exact this

/-- The initial state: only `start` is queued. -/
def hsearch_bq_initial (start : V) (d : ℕ × ℕ) (te : ℕ) : hsearch_bq_state V heur :=
  ⟨ofStored (hsearch_stored_state.initial heur start d te)
      (RQ.single bkey (((start, d), addH d (heur start)), 0)),
    ⟨hsearch_stored_state.initial heur start d te, _, rfl,
      (RQ.single_spec (key := bkey) (idx := bidx) (((start, d), addH d (heur start)), 0)).2, by
        rw [(RQ.single_spec (key := bkey) (idx := bidx) (((start, d), addH d (heur start)), 0)).1]
        simp [HeapQueue.sortedList, hsearch_stored_state.initial]⟩⟩

theorem hsearch_bq_initial_rel (start : V) (d : ℕ × ℕ) (te : ℕ) :
    BQRel (hsearch_bq_initial heur start d te).1 (hsearch_stored_state.initial heur start d te) :=
  ⟨_, rfl, (RQ.single_spec (key := bkey) (idx := bidx) (((start, d), addH d (heur start)), 0)).2, by
    rw [(RQ.single_spec (key := bkey) (idx := bidx) (((start, d), addH d (heur start)), 0)).1]
    simp [HeapQueue.sortedList, hsearch_stored_state.initial]⟩

theorem hsearch_bq_toBaseState_initial (start : V) (d : ℕ × ℕ) (te : ℕ) :
    has_base_search_state.to_base_state (G := G.toWeightedDiGraph) (D := ℕ × ℕ)
      (hsearch_bq_initial heur start d te) = base_search_state_initial start d := by
  rw [bq_to_base _ (hsearch_bq_initial_rel heur start d te)]
  exact hsearch_stored_toBaseState_initial G heur start d te

/-- **A\* with stored `f`-values on a bucket queue.** -/
def astar_bq_fastpath (start : V) (goal : V) (te : ℕ := 100) :
    Option ((G.toWeightedDiGraph).Path start goal) :=
  WeightedDiGraph.search_exe_with_step_eq_fast (G := G.toWeightedDiGraph) (start := start)
    (start_state := hsearch_bq_initial heur start ⟨0, 0⟩ te)
    (termination_metric := hsearch_bq_termination_metric G heur)
    (hsearch_step_expand_bq G heur) goal
    (hsearch_bq_step G heur) (hsearch_bq_step_eq G heur)
    (hsearch_bq_expand_metric_reduction G heur goal)
    (hsearch_bq_expand_keeps_base_invars G heur start goal)
    (hsearch_bq_toBaseState_initial G heur start (0, 0) te)

/-- **The bucket queue search returns the same path as `astar_heap_stored_fastpath`.** -/
theorem astar_bq_fastpath_eq_stored (start : V) (goal : V) (te : ℕ) :
    astar_bq_fastpath G heur start goal te = astar_heap_stored_fastpath G heur start goal te := by
  unfold astar_bq_fastpath astar_heap_stored_fastpath
  rw [WeightedDiGraph.search_exe_with_step_eq_fast_eq, WeightedDiGraph.search_exe_with_step_eq_fast_eq,
    WeightedDiGraph.search_exe_with_step_eq_stack, WeightedDiGraph.search_exe_with_step_eq_stack]
  exact search_exe_with_stack_step_sim_rel (G := G.toWeightedDiGraph) (D := ℕ × ℕ)
    (A := hsearch_bq_state V heur) (B := hsearch_stored_state V heur)
    (fun a b => BQRel a.1 b) (fun a b h => bq_to_base a h)
    (hsearch_step_expand_bq G heur) (hsearch_step_expand_stored G heur)
    (fun a b head tail h _ => bqExpand_rel G heur h head tail)
    (hsearch_bq_initial_rel heur start (0, 0) te)
    (hsearch_bq_termination_metric G heur) (hsearch_stored_termination_metric G heur)
    (hsearch_bq_expand_metric_reduction G heur goal)
    (hsearch_bq_expand_keeps_base_invars G heur start goal)
    (hsearch_bq_toBaseState_initial G heur start (0, 0) te)
    (hsearch_stored_expand_metric_reduction G heur goal)
    (hsearch_stored_expand_keeps_base_invars G heur start goal)
    (hsearch_stored_toBaseState_initial G heur start (0, 0) te)

end

/-- **The stored search runs on the bucket queue** (installed in `HeapLazyInfo` with the
single map instead). -/
theorem astar_heap_stored_fastpath_eq_bq :
    @astar_heap_stored_fastpath = @astar_bq_fastpath := by
  funext V _ _ _ _ G heur start goal te
  exact (astar_bq_fastpath_eq_stored G heur start goal te).symm


/-! ### Multi-goal search -/

section

variable (G : NatGraphWithGenerator V) (heur : V → ℕ∞)

/-- Multi-goal A* with stored `f`-values on a bucket queue. -/
def astar_multigoal_bq_fastpath (start : V)
    (is_goal : V → Prop) [DecidablePred is_goal] (te : ℕ := 100) :
    Option ((thegoal : {v : V // is_goal v}) × (G.toWeightedDiGraph).Path start thegoal) :=
  astar_multigoal_postprocess (g := G.toWeightedDiGraph) start is_goal
    (astar_bq_fastpath (add_artificial_goal_gen G is_goal) (opt_heur heur) (some start) none te)

theorem astar_multigoal_bq_fastpath_eq_stored (start : V)
    (is_goal : V → Prop) [DecidablePred is_goal] (te : ℕ) :
    astar_multigoal_bq_fastpath G heur start is_goal te
      = astar_multigoal_heap_stored_fastpath G heur start is_goal te := by
  unfold astar_multigoal_bq_fastpath astar_multigoal_heap_stored_fastpath
  rw [astar_bq_fastpath_eq_stored]

end

/-- **The multi-goal stored search runs on the bucket queue.** -/
theorem astar_multigoal_heap_stored_fastpath_eq_bq :
    @astar_multigoal_heap_stored_fastpath = @astar_multigoal_bq_fastpath := by
  funext V _ _ _ _ G heur start is_goal _ te
  exact (astar_multigoal_bq_fastpath_eq_stored G heur start is_goal te).symm

end NatGraph
