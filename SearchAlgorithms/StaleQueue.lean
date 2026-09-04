import SearchAlgorithms.HeapQueue

/-!
# Lazy deletion: a heap whose queue contains *stale* entries

`SearchAlgorithms.HeapQueue` says which list a heap of `(entry, sequence number)` pairs
represents: the entries in queue order.  The heap search of
`SearchAlgorithms.HeuristicSearchHeap` keeps that list in bijection with the queue of the
reference implementation, and therefore has to **rebuild** the heap whenever the expansion
changes the position of a node that is still queued (a *decrease-key*): the comparison
function of that heap reads the current path order, so changing the order can break the heap
invariant.

The implementation of `SearchAlgorithms.HeuristicSearchLazy` avoids the rebuild by *lazy
deletion*:

* every heap entry stores the key it was inserted with, so the comparison function never
  changes and the heap invariant can never be broken by an update of the path order;
* a decrease-key inserts a **new** entry and leaves the old one in the heap, where it becomes
  *stale*;
* stale entries are dropped when they reach the root (`purge`), which is `O(log m)` each and
  happens at most once per entry.

For that to be correct one needs to know that the stale entries are invisible: the queue of
the search is the list of the **live** entries, and dropping the stale ones from a heap
neither disturbs the order of the live ones nor depends on where the stale ones sit.  That is
the content of this file:

* `HeapQueue.liveQueue` — the queue represented by a heap *after* the stale entries have been
  removed;
* `HeapQueue.liveQueue_eq` — **the core lemma**: the live queue is exactly the stable sort
  (`List.mergeSort`) of the live entries, i.e. exactly the queue the reference implementation
  would have built;
* `HeapQueue.sortedList_deleteMin`, `liveQueue_deleteMin_of_stale`,
  `liveQueue_eq_cons_of_live` — popping: a stale root may be dropped without changing the
  live queue, and a live root *is* the head of the live queue;
* `HeapQueue.purge` — drop stale entries until the root is live, together with the facts that
  it preserves the live queue, the heap invariant and the entries (as a suffix of the queue).
-/

namespace SearchAlgorithms

namespace LHeap

variable {α : Type}

/-- The size of a heap is the number of its elements. -/
theorem size_eq_length_elems : ∀ h : LHeap α, h.size = h.elems.length
  | nil => rfl
  | node k x l r => by
    simp only [size_node, elems_node, List.length_cons, List.length_append,
      size_eq_length_elems l, size_eq_length_elems r]

theorem size_merge (le : α → α → Bool) (h₁ h₂ : LHeap α) :
    (merge le h₁ h₂).size = h₁.size + h₂.size := by
  rw [size_eq_length_elems, size_eq_length_elems, size_eq_length_elems,
    (elems_merge le h₁ h₂).length_eq, List.length_append]

/-- Removing the minimum makes the heap smaller. -/
theorem size_deleteMin_lt (le : α → α → Bool) (h : LHeap α) (x : α) (hx : h.peek = some x) :
    (deleteMin le h).size < h.size := by
  cases h with
  | nil => simp [peek] at hx
  | node k y l r => simp [deleteMin, size_merge]

end LHeap

namespace HeapQueue

open List

variable {α : Type}

/-!
## Filtering the queue
-/

/-- **Filtering commutes with the (decorated) sort.**  The sequence numbers are distinct, so
the sorted list is determined by its elements; removing some of them therefore gives the
sorted list of the remaining ones. -/
theorem mergeSort_filter_zipIdxLE (le : α → α → Bool)
    (trans : ∀ a b c, le a b → le b c → le a c)
    (total : ∀ a b, (le a b || le b a) = true)
    (p : α × ℕ → Bool) (d : List (α × ℕ)) (hnd : (d.map Prod.snd).Nodup) :
    (d.mergeSort (zipIdxLE le)).filter p = (d.filter p).mergeSort (zipIdxLE le) := by
  have hpermS : (d.mergeSort (zipIdxLE le)).Perm d := mergeSort_perm _ _
  refine SortAux.eq_of_perm_of_zipIdxLE le _ _ ?_ ?_ ?_ ?_
  · exact (hpermS.filter p).trans (mergeSort_perm _ _).symm
  · exact ((pairwise_mergeSort (zipIdxLE_trans trans) (zipIdxLE_total total) d).sublist
      List.filter_sublist)
  · exact pairwise_mergeSort (zipIdxLE_trans trans) (zipIdxLE_total total) _
  · refine List.Nodup.sublist ?_ ((hpermS.map Prod.snd).nodup_iff.mpr hnd)
    exact List.filter_sublist.map Prod.snd

/-- The sorted list of a heap is the sort of any list of its elements (the sequence numbers
being distinct, this determines it). -/
theorem sortedList_eq (le : α → α → Bool)
    (trans : ∀ a b c, le a b → le b c → le a c)
    (total : ∀ a b, (le a b || le b a) = true)
    (h : LHeap (α × ℕ)) (d : List (α × ℕ)) (hperm : h.elems.Perm d)
    (hnd : (d.map Prod.snd).Nodup) :
    sortedList le h = d.mergeSort (zipIdxLE le) := by
  refine SortAux.eq_of_perm_of_zipIdxLE le _ _
    (((sortedList_perm le h).trans hperm).trans (mergeSort_perm _ _).symm)
    (sortedList_pairwise le trans total h)
    (pairwise_mergeSort (zipIdxLE_trans trans) (zipIdxLE_total total) _) ?_
  exact ((((sortedList_perm le h).trans hperm).map Prod.snd).nodup_iff).mpr hnd

/-!
## The live queue
-/

/-- **The queue represented by a heap with lazy deletion**: the entries in queue order, with
the stale ones (those failing `p`) removed. -/
def liveQueue (le : α → α → Bool) (p : α × ℕ → Bool) (h : LHeap (α × ℕ)) : List α :=
  ((sortedList le h).filter p).map Prod.fst

/-- **The core lemma on staleness.**

The live queue of a heap is exactly the *stable sort* of its live entries: the stale entries
neither contribute to it nor influence the order of the live ones.  `d` is the list of all
entries of the heap in any order whose sequence numbers are distinct; the sequence numbers
only have to increase along the *live* entries that compare equal — nothing at all is assumed
about the stale ones. -/
theorem liveQueue_eq (le : α → α → Bool)
    (trans : ∀ a b c, le a b → le b c → le a c)
    (total : ∀ a b, (le a b || le b a) = true)
    (p : α × ℕ → Bool) (h : LHeap (α × ℕ)) (d : List (α × ℕ)) (hperm : h.elems.Perm d)
    (hnd : (d.map Prod.snd).Nodup)
    (htie : (d.filter p).Pairwise
      (fun a b => (le a.1 b.1 && le b.1 a.1) = true → a.2 ≤ b.2)) :
    liveQueue le p h = ((d.filter p).map Prod.fst).mergeSort le := by
  unfold liveQueue
  rw [sortedList_eq le trans total h d hperm hnd,
    mergeSort_filter_zipIdxLE le trans total _ d hnd,
    SortAux.mergeSort_map_fst_of_tie_le le _ htie]

/-- The live queue is empty exactly when no entry of the heap is live. -/
theorem liveQueue_eq_nil_iff (le : α → α → Bool) (p : α × ℕ → Bool) (h : LHeap (α × ℕ)) :
    liveQueue le p h = [] ↔ ∀ e ∈ h.elems, p e = false := by
  unfold liveQueue
  rw [List.map_eq_nil_iff, List.filter_eq_nil_iff]
  constructor
  · intro hs e he
    have : e ∈ sortedList le h := (sortedList_perm le h).mem_iff.mpr he
    simpa using hs e this
  · intro hs e he
    have : e ∈ h.elems := (sortedList_perm le h).mem_iff.mp he
    simp [hs e this]

/-!
## Popping
-/

/-- **Removing the root removes the head of the queue.** -/
theorem sortedList_deleteMin (le : α → α → Bool)
    (trans : ∀ a b c, le a b → le b c → le a c)
    (total : ∀ a b, (le a b || le b a) = true)
    (h : LHeap (α × ℕ)) (hord : LHeap.Ordered (zipIdxLE le) h)
    (hnd : (h.elems.map Prod.snd).Nodup) :
    sortedList le (LHeap.deleteMin (zipIdxLE le) h) = (sortedList le h).tail := by
  cases hpk : h.peek with
  | none =>
    have he : h.elems = [] := (LHeap.peek_eq_none_iff h).mp hpk
    cases h with
    | nil => simp [LHeap.deleteMin, sortedList, LHeap.elems]
    | node k x l r => simp [LHeap.elems] at he
  | some x =>
    obtain ⟨t, ht⟩ := sortedList_head le trans total h x hord hnd hpk
    have hpermt : (LHeap.deleteMin (zipIdxLE le) h).elems.Perm t := by
      have h1 : h.elems.Perm (x :: (LHeap.deleteMin (zipIdxLE le) h).elems) :=
        LHeap.elems_deleteMin _ h x hpk
      have h2 : h.elems.Perm (x :: t) := ((sortedList_perm le h).symm.trans (by rw [ht]))
      exact (List.Perm.cons_inv (h1.symm.trans h2))
    have hndt : (t.map Prod.snd).Nodup := by
      have hndS : ((sortedList le h).map Prod.snd).Nodup :=
        (((sortedList_perm le h).map Prod.snd).nodup_iff).mpr hnd
      rw [ht, List.map_cons] at hndS
      exact hndS.of_cons
    have hpt : t.Pairwise (fun a b => zipIdxLE le a b = true) := by
      have := sortedList_pairwise le trans total h
      rw [ht] at this
      exact (List.pairwise_cons.mp this).2
    rw [sortedList_eq le trans total _ t hpermt hndt, List.mergeSort_of_pairwise hpt, ht]
    simp

/-- Dropping a **stale** root does not change the live queue. -/
theorem liveQueue_deleteMin_of_stale (le : α → α → Bool)
    (trans : ∀ a b c, le a b → le b c → le a c)
    (total : ∀ a b, (le a b || le b a) = true)
    (p : α × ℕ → Bool) (h : LHeap (α × ℕ)) (hord : LHeap.Ordered (zipIdxLE le) h)
    (hnd : (h.elems.map Prod.snd).Nodup) (x : α × ℕ) (hpk : h.peek = some x)
    (hstale : p x = false) :
    liveQueue le p (LHeap.deleteMin (zipIdxLE le) h) = liveQueue le p h := by
  obtain ⟨t, ht⟩ := sortedList_head le trans total h x hord hnd hpk
  unfold liveQueue
  rw [sortedList_deleteMin le trans total h hord hnd, ht]
  simp [hstale]

/-- A **live** root is the head of the live queue. -/
theorem liveQueue_eq_cons_of_live (le : α → α → Bool)
    (trans : ∀ a b c, le a b → le b c → le a c)
    (total : ∀ a b, (le a b || le b a) = true)
    (p : α × ℕ → Bool) (h : LHeap (α × ℕ)) (hord : LHeap.Ordered (zipIdxLE le) h)
    (hnd : (h.elems.map Prod.snd).Nodup) (x : α × ℕ) (hpk : h.peek = some x)
    (hlive : p x = true) :
    liveQueue le p h = x.1 :: liveQueue le p (LHeap.deleteMin (zipIdxLE le) h) := by
  obtain ⟨t, ht⟩ := sortedList_head le trans total h x hord hnd hpk
  unfold liveQueue
  rw [sortedList_deleteMin le trans total h hord hnd, ht]
  simp [hlive]

/-!
## Purging the stale entries at the root
-/

/-- Drop the entries at the root of the heap until the root is live (or the heap is empty).
Every entry is dropped at most once during the whole search, so this costs `O(log m)`
amortised. -/
def purge (le : α → α → Bool) (p : α × ℕ → Bool) (h : LHeap (α × ℕ)) : LHeap (α × ℕ) :=
  match hpk : h.peek with
  | none => h
  | some x =>
    if p x then h
    else
      have _hlt : (LHeap.deleteMin (zipIdxLE le) h).size < h.size :=
        LHeap.size_deleteMin_lt _ h x hpk
      purge le p (LHeap.deleteMin (zipIdxLE le) h)
termination_by h.size

/-- After purging, the root is live (if there is one). -/
theorem peek_purge_live (le : α → α → Bool) (p : α × ℕ → Bool) (h : LHeap (α × ℕ)) (x : α × ℕ)
    (hpk : (purge le p h).peek = some x) : p x = true := by
  unfold purge at hpk
  split at hpk
  · next hnone => rw [hnone] at hpk; exact absurd hpk (by simp)
  · next y hy =>
    split at hpk
    · next hlive =>
      rw [hy] at hpk
      obtain rfl : y = x := Option.some.inj hpk
      exact hlive
    · exact peek_purge_live le p _ x hpk
termination_by h.size
decreasing_by
  next hy _ => exact LHeap.size_deleteMin_lt _ h _ hy

/-- Purging keeps every live entry: only stale entries are dropped. -/
theorem mem_purge_of_live (le : α → α → Bool) (p : α × ℕ → Bool) (h : LHeap (α × ℕ))
    {e : α × ℕ} (he : e ∈ h.elems) (hpe : p e = true) : e ∈ (purge le p h).elems := by
  unfold purge
  split
  · exact he
  · next y hy =>
    split
    · exact he
    · next hstale =>
      refine mem_purge_of_live le p _ ?_ hpe
      have h1 : h.elems.Perm (y :: (LHeap.deleteMin (zipIdxLE le) h).elems) :=
        LHeap.elems_deleteMin _ h y hy
      rcases List.mem_cons.mp (h1.mem_iff.mp he) with rfl | h2
      · exact absurd hpe hstale
      · exact h2
termination_by h.size
decreasing_by
  next hy _ => exact LHeap.size_deleteMin_lt _ h _ hy

/-- Purging preserves the heap invariant. -/
theorem Ordered_purge (le : α → α → Bool)
    (trans : ∀ a b c, le a b → le b c → le a c)
    (total : ∀ a b, (le a b || le b a) = true)
    (p : α × ℕ → Bool) (h : LHeap (α × ℕ)) (hord : LHeap.Ordered (zipIdxLE le) h) :
    LHeap.Ordered (zipIdxLE le) (purge le p h) := by
  unfold purge
  split
  · exact hord
  · next y hy =>
    split
    · exact hord
    · exact Ordered_purge le trans total p _
        (LHeap.Ordered_deleteMin _ (zipIdxLE_total total) (zipIdxLE_trans trans) h hord)
termination_by h.size
decreasing_by
  next hy _ => exact LHeap.size_deleteMin_lt _ h _ hy

/-- The queue of the purged heap is a *suffix* of the queue: purging only removes entries,
and only from the front. -/
theorem sortedList_purge_suffix (le : α → α → Bool)
    (trans : ∀ a b c, le a b → le b c → le a c)
    (total : ∀ a b, (le a b || le b a) = true)
    (p : α × ℕ → Bool) (h : LHeap (α × ℕ)) (hord : LHeap.Ordered (zipIdxLE le) h)
    (hnd : (h.elems.map Prod.snd).Nodup) :
    (sortedList le (purge le p h)).IsSuffix (sortedList le h) := by
  unfold purge
  split
  · exact List.suffix_rfl
  · next y hy =>
    split
    · exact List.suffix_rfl
    · have hnd' : ((LHeap.deleteMin (zipIdxLE le) h).elems.map Prod.snd).Nodup := by
        have h1 : h.elems.Perm (y :: (LHeap.deleteMin (zipIdxLE le) h).elems) :=
          LHeap.elems_deleteMin _ h y hy
        have := ((h1.map Prod.snd).nodup_iff).mp hnd
        simpa using this.of_cons
      refine List.IsSuffix.trans
        (sortedList_purge_suffix le trans total p _
          (LHeap.Ordered_deleteMin _ (zipIdxLE_total total) (zipIdxLE_trans trans) h hord) hnd')
        ?_
      rw [sortedList_deleteMin le trans total h hord hnd]
      exact List.tail_suffix _
termination_by h.size
decreasing_by
  next hy _ => exact LHeap.size_deleteMin_lt _ h _ hy

/-- Every entry of the purged heap is an entry of the heap. -/
theorem mem_of_mem_purge (le : α → α → Bool)
    (trans : ∀ a b c, le a b → le b c → le a c)
    (total : ∀ a b, (le a b || le b a) = true)
    (p : α × ℕ → Bool) (h : LHeap (α × ℕ)) (hord : LHeap.Ordered (zipIdxLE le) h)
    (hnd : (h.elems.map Prod.snd).Nodup) {e : α × ℕ} (he : e ∈ (purge le p h).elems) :
    e ∈ h.elems := by
  have h1 : e ∈ sortedList le (purge le p h) :=
    (sortedList_perm le (purge le p h)).mem_iff.mpr he
  have h2 : e ∈ sortedList le h :=
    ((sortedList_purge_suffix le trans total p h hord hnd).subset) h1
  exact (sortedList_perm le h).mem_iff.mp h2

/-- The sequence numbers of the purged heap are still distinct. -/
theorem nodup_snd_purge (le : α → α → Bool)
    (trans : ∀ a b c, le a b → le b c → le a c)
    (total : ∀ a b, (le a b || le b a) = true)
    (p : α × ℕ → Bool) (h : LHeap (α × ℕ)) (hord : LHeap.Ordered (zipIdxLE le) h)
    (hnd : (h.elems.map Prod.snd).Nodup) :
    ((purge le p h).elems.map Prod.snd).Nodup := by
  have hs : ((sortedList le h).map Prod.snd).Nodup :=
    (((sortedList_perm le h).map Prod.snd).nodup_iff).mpr hnd
  have h1 : ((sortedList le (purge le p h)).map Prod.snd).Nodup :=
    hs.sublist (((sortedList_purge_suffix le trans total p h hord hnd).sublist).map Prod.snd)
  exact (((sortedList_perm le (purge le p h)).map Prod.snd).nodup_iff).mp h1

/-- **Purging does not change the live queue** — the stale entries it removes were invisible
anyway. -/
theorem liveQueue_purge (le : α → α → Bool)
    (trans : ∀ a b c, le a b → le b c → le a c)
    (total : ∀ a b, (le a b || le b a) = true)
    (p : α × ℕ → Bool) (h : LHeap (α × ℕ)) (hord : LHeap.Ordered (zipIdxLE le) h)
    (hnd : (h.elems.map Prod.snd).Nodup) :
    liveQueue le p (purge le p h) = liveQueue le p h := by
  unfold purge
  split
  · rfl
  · next y hy =>
    split
    · rfl
    · next hstale =>
      have hnd' : ((LHeap.deleteMin (zipIdxLE le) h).elems.map Prod.snd).Nodup := by
        have h1 : h.elems.Perm (y :: (LHeap.deleteMin (zipIdxLE le) h).elems) :=
          LHeap.elems_deleteMin _ h y hy
        have := ((h1.map Prod.snd).nodup_iff).mp hnd
        simpa using this.of_cons
      rw [liveQueue_purge le trans total p _
        (LHeap.Ordered_deleteMin _ (zipIdxLE_total total) (zipIdxLE_trans trans) h hord) hnd']
      exact liveQueue_deleteMin_of_stale le trans total p h hord hnd y hy
        (by simpa using hstale)
termination_by h.size
decreasing_by
  next hy _ => exact LHeap.size_deleteMin_lt _ h _ hy

end HeapQueue

end SearchAlgorithms
