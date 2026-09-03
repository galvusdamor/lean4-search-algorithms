import Mathlib.Tactic

/-!
# Splitting a `mergeSort` into a `merge`

`List.mergeSort` is *stable*: the output is the unique sorted permutation of the input in
which elements that compare equal keep their input order.  Consequently sorting a
concatenation is the same as merging the two sorted halves:

```
(xs ++ ys).mergeSort le = (xs.mergeSort le).merge (ys.mergeSort le) le
```

(`mergeSort_append`, for a transitive and total comparison function).  The special case in
which `xs` is already sorted,

```
(xs ++ ys).mergeSort le = xs.merge (ys.mergeSort le) le
```

(`mergeSort_append_of_pairwise_left`), is what makes it possible to *maintain* a sorted
search queue instead of re-sorting it from scratch after every expansion: appending `k` new
nodes to a queue of length `m` costs one `merge`, i.e. `O(k + position of the last
insertion)` comparisons — and, in particular, `O(1)` when no node is added — instead of the
`Θ(m log m)` comparisons of a full `mergeSort`.

The proofs go through the stability lemmas of the Lean core library (`mergeSort_zipIdx`,
`merge_stable`), which express stability by tagging every element with its position.
-/

namespace SortAux

open List

/-- Shifting the starting index of `zipIdx` shifts all indices. -/
theorem zipIdx_shift {α : Type} (l : List α) (i k : ℕ) :
    l.zipIdx (i + k) = (l.zipIdx i).map (fun p => (p.1, p.2 + k)) := by
  induction l generalizing i with
  | nil => simp
  | cons a t ih =>
    simp only [zipIdx_cons, List.map_cons]
    congr 1
    rw [show i + k + 1 = (i + 1) + k by omega, ih]

/-- Stability of `mergeSort`, with an arbitrary starting index: sorting the index-tagged list
and forgetting the indices is the same as sorting the list. -/
theorem mergeSort_zipIdx_shift {α : Type} (le : α → α → Bool) (k : ℕ) (l : List α) :
    ((l.zipIdx k).mergeSort (zipIdxLE le)).map (fun p => p.1) = l.mergeSort le := by
  have h0 : l.zipIdx k = (l.zipIdx 0).map (fun p => (p.1, p.2 + k)) := by
    have := zipIdx_shift l 0 k
    simpa using this
  rw [h0, ← map_mergeSort (f := fun p : α × ℕ => (p.1, p.2 + k)) (r := zipIdxLE le)
    (s := zipIdxLE le) (l := l.zipIdx 0) (by intro a _ b _; simp [zipIdxLE])]
  rw [List.map_map]
  exact mergeSort_zipIdx

/-- **Sorting a concatenation is merging the sorted parts.** -/
theorem mergeSort_append {α : Type} (le : α → α → Bool)
    (trans : ∀ a b c, le a b → le b c → le a c)
    (total : ∀ a b, (le a b || le b a) = true) (xs ys : List α) :
    (xs ++ ys).mergeSort le = (xs.mergeSort le).merge (ys.mergeSort le) le := by
  set A : List (α × ℕ) := (xs.zipIdx 0).mergeSort (zipIdxLE le) with hA
  set B : List (α × ℕ) := (ys.zipIdx xs.length).mergeSort (zipIdxLE le) with hB
  have hidxA : ∀ x ∈ A, x.2 < xs.length := by
    intro x hx
    have hx' : x ∈ xs.zipIdx 0 := (mergeSort_perm _ _).mem_iff.mp hx
    obtain ⟨-, h2, -⟩ := mem_zipIdx (x := x.1) (i := x.2) (by simpa using hx')
    simpa using h2
  have hidxB : ∀ x ∈ B, xs.length ≤ x.2 := by
    intro x hx
    have hx' : x ∈ ys.zipIdx xs.length := (mergeSort_perm _ _).mem_iff.mp hx
    obtain ⟨h1, -, -⟩ := mem_zipIdx (x := x.1) (i := x.2) (by simpa using hx')
    exact h1
  have key : ((xs ++ ys).zipIdx 0).mergeSort (zipIdxLE le) = A.merge B (zipIdxLE le) := by
    have hperm :
        (((xs ++ ys).zipIdx 0).mergeSort (zipIdxLE le)).Perm (A.merge B (zipIdxLE le)) := by
      refine (mergeSort_perm _ _).trans ?_
      refine Perm.trans ?_ (merge_perm_append (le := zipIdxLE le)).symm
      rw [zipIdx_append]
      simp only [Nat.zero_add]
      exact Perm.append (mergeSort_perm _ _).symm (mergeSort_perm _ _).symm
    refine Perm.eq_of_pairwise (le := fun a b => zipIdxLE le a b = true) ?_ ?_ ?_ hperm
    · intro a b ha hb hab hba
      have h2 : a.2 = b.2 := by
        simp only [zipIdxLE] at hab hba
        by_cases h1 : le a.1 b.1
        · by_cases h2 : le b.1 a.1
          · simp [h1, h2] at hab hba; omega
          · simp [h2] at hba
        · simp [h1] at hab
      have hma : a ∈ (xs ++ ys).zipIdx 0 := (mergeSort_perm _ _).mem_iff.mp ha
      have hmb : b ∈ (xs ++ ys).zipIdx 0 := (mergeSort_perm _ _).mem_iff.mp (hperm.mem_iff.mpr hb)
      obtain ⟨-, -, e1⟩ := mem_zipIdx (x := a.1) (i := a.2) (by simpa using hma)
      obtain ⟨-, -, e2⟩ := mem_zipIdx (x := b.1) (i := b.2) (by simpa using hmb)
      have h1 : a.1 = b.1 := by simp only [e1, e2, h2]
      exact Prod.ext h1 h2
    · exact pairwise_mergeSort (zipIdxLE_trans trans) (zipIdxLE_total total) _
    · exact pairwise_merge (zipIdxLE_trans trans) (zipIdxLE_total total) _ _
        (pairwise_mergeSort (zipIdxLE_trans trans) (zipIdxLE_total total) _)
        (pairwise_mergeSort (zipIdxLE_trans trans) (zipIdxLE_total total) _)
  have hmap := congrArg (fun l => List.map (fun x : α × ℕ => x.1) l) key
  rw [merge_stable A B
    (fun x y hx hy => le_of_lt (lt_of_lt_of_le (hidxA x hx) (hidxB y hy)))] at hmap
  rw [hA, hB, mergeSort_zipIdx_shift le 0 xs, mergeSort_zipIdx_shift le xs.length ys,
    mergeSort_zipIdx_shift le 0 (xs ++ ys)] at hmap
  exact hmap

/-- **If the left list is already sorted, sorting a concatenation is a single `merge`.** -/
theorem mergeSort_append_of_pairwise_left {α : Type} (le : α → α → Bool)
    (trans : ∀ a b c, le a b → le b c → le a c)
    (total : ∀ a b, (le a b || le b a) = true) {xs : List α} (ys : List α)
    (hxs : xs.Pairwise (fun a b => le a b = true)) :
    (xs ++ ys).mergeSort le = xs.merge (ys.mergeSort le) le := by
  rw [mergeSort_append le trans total, mergeSort_of_pairwise hxs]

end SortAux
