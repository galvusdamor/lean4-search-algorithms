import SearchAlgorithms.LeftistHeap
import SearchAlgorithms.StableSortLemmas

/-!
# A heap as a search queue

A search queue that is kept as a *sorted list* has to pay `O(m)` for an insertion into a
queue of length `m` (`SearchAlgorithms.HeuristicSearchSorted`).  A heap pays `O(log m)`, but
it does not store a list at all — so to keep the correctness proofs of the reference
implementation one has to say which list a heap *represents*.

That is what this file does.  The elements of the heap are pairs `(a, n)` of a queue entry
and its **sequence number**, and the heap is ordered by `List.zipIdxLE le`, the
lexicographic order used by the Lean core library to state the stability of `mergeSort`.
The queue represented by a heap is

```
HeapQueue.toQueue le h = ((h.elems).mergeSort (zipIdxLE le)).map Prod.fst
```

and the two facts that make it usable are

* `HeapQueue.toQueue_eq`: if the elements of the heap are (a permutation of) a list `d` whose
  sequence numbers are distinct and increase along tied entries, then
  `toQueue le h = (d.map Prod.fst).mergeSort le`, i.e. the heap represents exactly the
  *stably sorted* queue of the reference implementation;
* `HeapQueue.sortedList_head`: the root of the heap is the first entry of that queue, so the
  search loop can read the next node to expand off the heap in `O(1)` without ever building
  the sorted list.

Only `toQueue` mentions `mergeSort`, and `toQueue` is never evaluated during the search: it
is the *specification* of the heap, computed only when the final abstract state is inspected.
-/

namespace SearchAlgorithms

namespace HeapQueue

open List

variable {α : Type}

/-- The elements of the heap in queue order. -/
def sortedList (le : α → α → Bool) (h : LHeap (α × ℕ)) : List (α × ℕ) :=
  h.elems.mergeSort (zipIdxLE le)

/-- The queue represented by the heap. -/
def toQueue (le : α → α → Bool) (h : LHeap (α × ℕ)) : List α :=
  (sortedList le h).map Prod.fst

theorem sortedList_perm (le : α → α → Bool) (h : LHeap (α × ℕ)) :
    (sortedList le h).Perm h.elems := mergeSort_perm _ _

theorem sortedList_pairwise (le : α → α → Bool)
    (trans : ∀ a b c, le a b → le b c → le a c)
    (total : ∀ a b, (le a b || le b a) = true) (h : LHeap (α × ℕ)) :
    (sortedList le h).Pairwise (fun a b => zipIdxLE le a b = true) :=
  pairwise_mergeSort (zipIdxLE_trans trans) (zipIdxLE_total total) _

/-- A list sorted by `zipIdxLE le` has increasing sequence numbers along tied entries. -/
theorem tie_le_of_pairwise (le : α → α → Bool) (l : List (α × ℕ))
    (h : l.Pairwise (fun a b => zipIdxLE le a b = true)) :
    l.Pairwise (fun a b => (le a.1 b.1 && le b.1 a.1) = true → a.2 ≤ b.2) := by
  refine h.imp ?_
  intro a b hab htie
  simp only [Bool.and_eq_true] at htie
  unfold zipIdxLE at hab
  simp only [htie.1, htie.2, if_true, decide_eq_true_eq] at hab
  exact hab

/-- **The queue represented by a heap is the stable sort of its elements.**

`d` is the queue as the reference implementation sees it (before sorting): its sequence
numbers have to be distinct and to increase along entries that compare equal. -/
theorem toQueue_eq (le : α → α → Bool)
    (trans : ∀ a b c, le a b → le b c → le a c)
    (total : ∀ a b, (le a b || le b a) = true)
    (h : LHeap (α × ℕ)) (d : List (α × ℕ)) (hperm : h.elems.Perm d)
    (hnd : (d.map Prod.snd).Nodup)
    (htie : d.Pairwise (fun a b => (le a.1 b.1 && le b.1 a.1) = true → a.2 ≤ b.2)) :
    toQueue le h = (d.map Prod.fst).mergeSort le := by
  have hp : (sortedList le h).Perm (d.mergeSort (zipIdxLE le)) :=
    ((sortedList_perm le h).trans hperm).trans (mergeSort_perm _ _).symm
  have h1 : sortedList le h = d.mergeSort (zipIdxLE le) := by
    refine SortAux.eq_of_perm_of_zipIdxLE le _ _ hp (sortedList_pairwise le trans total h)
      (pairwise_mergeSort (zipIdxLE_trans trans) (zipIdxLE_total total) _) ?_
    exact ((((sortedList_perm le h).trans hperm).map Prod.snd).nodup_iff).mpr hnd
  rw [toQueue, h1, SortAux.mergeSort_map_fst_of_tie_le le d htie]

/-- The queue is empty exactly when the heap is. -/
theorem toQueue_eq_nil_iff (le : α → α → Bool) (h : LHeap (α × ℕ)) :
    toQueue le h = [] ↔ h.peek = none := by
  rw [LHeap.peek_eq_none_iff, toQueue, List.map_eq_nil_iff]
  constructor
  · intro hs
    have hp : ([] : List (α × ℕ)).Perm h.elems := hs ▸ (sortedList_perm le h)
    exact hp.nil_eq.symm
  · intro he
    have hp : (sortedList le h).Perm [] := he ▸ (sortedList_perm le h)
    exact hp.eq_nil

/-- **The root of the heap is the first entry of the queue.** -/
theorem sortedList_head (le : α → α → Bool)
    (trans : ∀ a b c, le a b → le b c → le a c)
    (total : ∀ a b, (le a b || le b a) = true)
    (h : LHeap (α × ℕ)) (x : α × ℕ) (hord : LHeap.Ordered (zipIdxLE le) h)
    (hnd : (h.elems.map Prod.snd).Nodup) (hx : h.peek = some x) :
    ∃ t, sortedList le h = x :: t := by
  have hxmem : x ∈ h.elems := by
    obtain ⟨t, ht⟩ := (LHeap.peek_eq_some_iff h x).mp hx
    rw [ht]; exact List.mem_cons_self ..
  have hperm := sortedList_perm le h
  cases hs : sortedList le h with
  | nil =>
    exact absurd (hperm.mem_iff.mpr hxmem) (by rw [hs]; simp)
  | cons y t =>
    have hymem : y ∈ h.elems := hperm.mem_iff.mp (by rw [hs]; exact List.mem_cons_self ..)
    have hxy : x = y := by
      rcases LHeap.peek_le (zipIdxLE le) h hord x hx y hymem with h1 | h1
      · -- `x` is the root, so it is `≤ y`
        have h2 : zipIdxLE le y x = true := by
          have hxs : x ∈ sortedList le h := hperm.mem_iff.mpr hxmem
          rw [hs] at hxs
          rcases List.mem_cons.mp hxs with rfl | hxt
          · exact h1
          · have := sortedList_pairwise le trans total h
            rw [hs] at this
            exact (List.pairwise_cons.mp this).1 x hxt
        exact SortAux.eq_of_snd_eq hnd hxmem hymem (SortAux.zipIdxLE_antisymm_snd le x y h1 h2)
      · exact h1.symm
    exact ⟨t, by rw [hxy]⟩

end HeapQueue

end SearchAlgorithms
