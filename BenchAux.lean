import Mathlib

/-!
# Auxiliary facts for the Dijkstra benchmark

This file proves that the coerced `FinEnum` enumeration of `Fin n` equals `List.finRange n`.
The benchmark uses it to build arbitrarily large `Fin n` sparse graphs *without* a per-size
`by decide` (which does not scale), by discharging the `neighbours_sublist` field of
`WeightedDiGraphWithGenerator` with a size-independent proof.
-/

/-- The enumeration of a `FinEnum` built by `FinEnum.ofList` is the deduplicated list. -/
theorem finEnum_ofList_toList {α : Type} [DecidableEq α] (xs : List α) (h : ∀ x, x ∈ xs) :
    @FinEnum.toList α (FinEnum.ofList xs h) = xs.dedup := by
  have h1 : @FinEnum.toList α (FinEnum.ofList xs h)
      = List.map (xs.dedup.get) (List.finRange xs.dedup.length) := rfl
  rw [h1, List.map_get_finRange]
/-- The type-level `FinEnum` enumeration of `Fin n` is `List.finRange n`. -/
theorem finEnum_toList_fin (n : ℕ) : FinEnum.toList (Fin n) = List.finRange n := by
  rw [show (FinEnum.toList (Fin n))
      = @FinEnum.toList (Fin n) (FinEnum.ofList (List.finRange n) (by simp)) from rfl,
    finEnum_ofList_toList]
  exact List.Nodup.dedup (List.nodup_finRange n)

/-- The `FinEnum` enumeration of the subtype `↥(univ : Finset (Fin n))`. -/
theorem toList_subtype_univ (n : ℕ) :
    (FinEnum.toList (↥(Finset.univ : Finset (Fin n))))
      = (List.finRange n).map (fun x => ⟨x, Finset.mem_univ x⟩) := by
  rw [show (FinEnum.toList (↥(Finset.univ : Finset (Fin n))))
      = @FinEnum.toList _ (FinEnum.ofList
          ((FinEnum.toList (Fin n)).filterMap
            fun x => if h : x ∈ (Finset.univ : Finset (Fin n)) then some ⟨x, h⟩ else none)
          (by rintro ⟨x, h⟩; simp)) from rfl,
    finEnum_ofList_toList, finEnum_toList_fin]
  rw [show ((List.finRange n).filterMap
      fun x => if h : x ∈ (Finset.univ : Finset (Fin n)) then
        some (⟨x, h⟩ : ↥(Finset.univ : Finset (Fin n))) else none)
      = (List.finRange n).map (fun x => ⟨x, Finset.mem_univ x⟩) from by
        rw [List.filterMap_eq_map_iff_forall_eq_some.mpr]; intro a _; simp]
  exact List.Nodup.dedup ((List.nodup_finRange n).map (fun a b h => by simpa using h))

/-- The coerced `FinEnum` enumeration of all vertices of `Fin n` (as it appears in the
`neighbours_sublist` field of `WeightedDiGraphWithGenerator`) is `List.finRange n`. -/
theorem toList_univ_eq_finRange (n : ℕ) :
    (FinEnum.toList (Finset.univ : Finset (Fin n)) : List (Fin n)) = List.finRange n := by
  have hcoe : (FinEnum.toList (Finset.univ : Finset (Fin n)) : List (Fin n))
      = (FinEnum.toList (↥(Finset.univ : Finset (Fin n)))).map (Subtype.val) := by
    rw [bind_pure_comp, List.map_eq_map]
  rw [hcoe, toList_subtype_univ, List.map_map]
  exact List.map_id _

/-- Variant of `toList_univ_eq_finRange` for the `Fintype` instance coming from `FinEnum`
(`FinEnum.instFintype`), which is the one appearing in the `neighbours_sublist` field of
`WeightedDiGraphWithGenerator` (that structure only has `[FinEnum V]` in scope).  The two
`Fintype (Fin n)` instances are equal since `Fintype` is a subsingleton. -/
theorem toList_univ_finEnum_eq_finRange (n : ℕ) :
    (FinEnum.toList (@Finset.univ (Fin n) FinEnum.instFintype) : List (Fin n)) = List.finRange n := by
  rw [Subsingleton.elim (FinEnum.instFintype) (Fin.fintype n)]
  exact toList_univ_eq_finRange n
/-- A strictly increasing list of vertices is a sublist of `List.finRange n`.  This discharges
the `neighbours_sublist` field of `WeightedDiGraphWithGenerator` for *any* neighbour function
that lists its neighbours in increasing order, again with a size-independent proof. -/
theorem sublist_finRange_of_pairwise_lt {n : ℕ} (l : List (Fin n))
    (h : l.Pairwise (· < ·)) : l.Sublist (List.finRange n) := by
  have hnd : l.Nodup := h.imp (fun {_ _} hab => ne_of_lt hab)
  have hsub : l ⊆ List.finRange n := fun x _ => List.mem_finRange x
  have hsp : l.Subperm (List.finRange n) := List.subperm_of_subset hnd hsub
  have h1 : l.SortedLE := List.sortedLE_iff_pairwise.mpr (h.imp (fun {_ _} hab => le_of_lt hab))
  have h2 : (List.finRange n).SortedLE := List.sortedLE_iff_pairwise.mpr
    ((List.pairwise_lt_finRange n).imp (fun {_ _} hab => le_of_lt hab))
  exact List.sublist_of_subperm_of_sortedLE hsp h1 h2
