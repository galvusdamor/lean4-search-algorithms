import SearchAlgorithms.MergeSortLemmas

/-!
# Sorting decorated lists: from a heap back to the stable `mergeSort`

The search queue of `SearchAlgorithms.HeuristicSearchSorted` is a list kept sorted by
`List.mergeSort`, which is *stable*: elements that compare equal keep the order they had in
the input.  A heap, on the other hand, knows nothing about insertion order, so on its own it
cannot reproduce the queue of the reference implementation — only a permutation of it.

The standard fix is used here: every queue entry carries a **sequence number**, and the heap
compares `(vertex, sequence number)` pairs lexicographically, i.e. with the comparator
`List.zipIdxLE le` that the Lean core library already uses to *state* the stability of
`mergeSort`.  Two facts are then needed, and both are proved in this file for an arbitrary
comparison function `le` on the undecorated elements:

* `SortAux.eq_of_perm_of_zipIdxLE` — with pairwise distinct sequence numbers, `zipIdxLE le`
  is antisymmetric, so a *sorted* list is determined by its elements: any two sorted
  permutations of each other are equal.  This is what lets one replace "the list obtained by
  emptying the heap" by "the sorted list of the elements of the heap".
* `SortAux.mergeSort_map_fst_of_tie_le` — if in the input list the sequence numbers increase
  along every class of tied elements, then sorting the decorated list and forgetting the
  decorations gives exactly the *stable* sort of the undecorated list.

Together they say: a heap of `(vertex, sequence number)` pairs whose sequence numbers respect
the queue order represents exactly the sorted queue of the reference implementation.
-/

namespace SortAux

open List MergeSort.Internal

variable {α : Type}

/-!
## `zipIdxLE` is antisymmetric on the decorations
-/

/-- If two decorated elements compare `≤` in both directions, their decorations agree. -/
theorem zipIdxLE_antisymm_snd (le : α → α → Bool) (a b : α × ℕ)
    (hab : zipIdxLE le a b = true) (hba : zipIdxLE le b a = true) : a.2 = b.2 := by
  unfold zipIdxLE at hab hba
  by_cases h1 : le a.1 b.1
  · by_cases h2 : le b.1 a.1
    · simp only [h1, h2, if_true, decide_eq_true_eq] at hab hba
      omega
    · simp [h2] at hba
  · simp [h1] at hab

/-- In a list with pairwise distinct decorations, an element is determined by its
decoration. -/
theorem eq_of_snd_eq {l : List (α × ℕ)} (hnd : (l.map Prod.snd).Nodup)
    {a b : α × ℕ} (ha : a ∈ l) (hb : b ∈ l) (h : a.2 = b.2) : a = b :=
  List.inj_on_of_nodup_map hnd ha hb h

/-- **A sorted list is determined by its elements** (when the decorations are distinct):
two lists that are permutations of each other and both sorted by `zipIdxLE le` are equal. -/
theorem eq_of_perm_of_zipIdxLE (le : α → α → Bool) (l₁ l₂ : List (α × ℕ))
    (hp : l₁.Perm l₂)
    (h₁ : l₁.Pairwise (fun a b => zipIdxLE le a b = true))
    (h₂ : l₂.Pairwise (fun a b => zipIdxLE le a b = true))
    (hnd : (l₁.map Prod.snd).Nodup) : l₁ = l₂ := by
  refine List.Perm.eq_of_pairwise ?_ h₁ h₂ hp
  intro a b ha hb hab hba
  exact eq_of_snd_eq hnd ha (hp.mem_iff.mpr hb) (zipIdxLE_antisymm_snd le a b hab hba)

/-!
## Decorating a list with consecutive numbers
-/

/-- The decorations of `l.zipIdx n` increase strictly. -/
theorem zipIdx_pairwise_snd_lt {β : Type} (l : List β) (n : ℕ) :
    (l.zipIdx n).Pairwise (fun a b => a.2 < b.2) := by
  induction l generalizing n with
  | nil => simp
  | cons a t ih =>
    rw [List.zipIdx_cons, List.pairwise_cons]
    refine ⟨?_, ih (n + 1)⟩
    intro b hb
    obtain ⟨h1, -, -⟩ := List.mem_zipIdx (x := b.1) (i := b.2) (by simpa using hb)
    simpa using h1

/-- The decorations of `l.zipIdx n` lie in `[n, n + l.length)`. -/
theorem mem_zipIdx_bounds {β : Type} {l : List β} {n : ℕ} {p : β × ℕ} (hp : p ∈ l.zipIdx n) :
    n ≤ p.2 ∧ p.2 < n + l.length := by
  obtain ⟨h1, h2, -⟩ := List.mem_zipIdx (x := p.1) (i := p.2) (by simpa using hp)
  exact ⟨h1, h2⟩

/-!
## Sorting a decorated list is the stable sort of the undecorated one
-/

private theorem pairwise_cross {P : α × ℕ → α × ℕ → Prop} {d : List (α × ℕ)}
    (h : d.Pairwise P) (n : ℕ) : ∀ a ∈ d.take n, ∀ b ∈ d.drop n, P a b := by
  have h' : (d.take n ++ d.drop n).Pairwise P := by rwa [List.take_append_drop]
  exact (List.pairwise_append.mp h').2.2

/-- **Sorting the decorated list and forgetting the decorations is the stable sort.**

The hypothesis is that in the input list the decorations increase along every class of tied
elements — which is exactly what holds for a search queue whose entries are numbered in the
order in which they entered it. -/
theorem mergeSort_map_fst_of_tie_le (le : α → α → Bool) :
    ∀ (d : List (α × ℕ)),
      d.Pairwise (fun a b => (le a.1 b.1 && le b.1 a.1) = true → a.2 ≤ b.2) →
      (d.mergeSort (zipIdxLE le)).map Prod.fst = (d.map Prod.fst).mergeSort le
  | [], _ => by simp
  | [x], _ => by simp
  | a :: b :: l, h => by
    have hcross : ∀ p ∈ (a :: b :: l).take (((a :: b :: l).length + 1) / 2), ∀ q ∈
        (a :: b :: l).drop (((a :: b :: l).length + 1) / 2),
        zipIdxLE le p q = le p.1 q.1 := by
      intro p hp q hq
      have := pairwise_cross h (((a :: b :: l).length + 1) / 2) p hp q hq
      unfold zipIdxLE
      by_cases h1 : le p.1 q.1
      · by_cases h2 : le q.1 p.1
        · simp only [h1, h2, if_true]
          simp [this (by simp [h1, h2])]
        · simp [h1, h2]
      · simp [h1]
    have htake : ((a :: b :: l).take (((a :: b :: l).length + 1) / 2)).Pairwise
        (fun a b => (le a.1 b.1 && le b.1 a.1) = true → a.2 ≤ b.2) :=
      h.sublist (List.take_sublist _ _)
    have hdrop : ((a :: b :: l).drop (((a :: b :: l).length + 1) / 2)).Pairwise
        (fun a b => (le a.1 b.1 && le b.1 a.1) = true → a.2 ≤ b.2) :=
      h.sublist (List.drop_sublist _ _)
    simp only [List.mergeSort, splitInTwo_fst, splitInTwo_snd, List.map_cons]
    rw [map_merge (f := Prod.fst) (s := le)
      (fun p hp q hq => hcross p (by simpa using List.mem_mergeSort.mp hp)
        q (by simpa using List.mem_mergeSort.mp hq))]
    rw [mergeSort_map_fst_of_tie_le le _ htake, mergeSort_map_fst_of_tie_le le _ hdrop]
    simp only [List.map_take, List.map_drop, List.map_cons, List.length_cons, List.length_map]
  termination_by d => d.length
  decreasing_by
    · simp only [List.length_take, List.length_cons]; omega
    · simp only [List.length_drop, List.length_cons]; omega

end SortAux
