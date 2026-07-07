import Mathlib

/-!
# Auxiliary facts for the Dijkstra benchmark

This file proves that the coerced `FinEnum` enumeration of `Fin n` equals `List.finRange n`.
The benchmark uses it to build arbitrarily large `Fin n` sparse graphs *without* a per-size
`by decide` (which does not scale), by discharging the `neighbours_sublist` field of
`WeightedDiGraphWithGenerator` with a size-independent proof.
-/

/-- The type-level `FinEnum` enumeration of `Fin n` is `List.finRange n`. -/
theorem finEnum_toList_fin (n : ℕ) : FinEnum.toList (Fin n) = List.finRange n := by
  have hdedup : (List.finRange n).dedup = List.finRange n :=
    List.Nodup.dedup (List.nodup_finRange n)
  unfold FinEnum.toList
  show List.map (⇑(FinEnum.fin).equiv.symm) (List.finRange (FinEnum.fin.card)) = _
  unfold FinEnum.fin FinEnum.ofList
  simp only [FinEnum.ofNodupList, hdedup, Equiv.coe_fn_symm_mk]
  rw [List.map_get_finRange]; exact hdedup

/-- `Pairwise (· < ·)` for the value-projection of the enumeration of `↥univ`: the
enumeration is strictly increasing in the underlying `Fin n` value. -/
theorem pairwise_lt_map_val_toList_univ (n : ℕ) :
    List.Pairwise (· < ·)
      ((FinEnum.toList (↥(Finset.univ : Finset (Fin n)))).map Subtype.val) := by
  refine' List.pairwise_map.mpr _
  convert List.pairwise_lt_finRange n using 1
  have h_univ : FinEnum.toList (↥(Finset.univ : Finset (Fin n)))
      = List.map (fun x => ⟨x, by simp⟩) (List.finRange n) := by
    have h_eq : FinEnum.toList (Fin n) = List.finRange n := finEnum_toList_fin n
    convert List.map_get_finRange _ using 2
    rw [List.dedup_eq_self.mpr]
    · aesop
    · refine' List.Nodup.filterMap _ _
      · aesop
      · exact h_eq.symm ▸ List.nodup_finRange _
  grind

/-- The coerced `FinEnum` enumeration of all vertices of `Fin n` (as it appears in the
`neighbours_sublist` field of `WeightedDiGraphWithGenerator`) is `List.finRange n`. -/
theorem toList_univ_eq_finRange (n : ℕ) :
    (FinEnum.toList (Finset.univ : Finset (Fin n)) : List (Fin n)) = List.finRange n := by
  have hcoe : (FinEnum.toList (Finset.univ : Finset (Fin n)) : List (Fin n))
      = (FinEnum.toList (↥(Finset.univ : Finset (Fin n)))).map (Subtype.val) := by
    rw [bind_pure_comp, List.map_eq_map]
  rw [hcoe]
  have hnodup : ((FinEnum.toList (↥(Finset.univ : Finset (Fin n)))).map Subtype.val).Nodup :=
    (FinEnum.nodup_toList).map (fun a b h => Subtype.ext h)
  refine List.Perm.eq_of_pairwise (le := (· < ·))
    (fun a b _ _ hab hba => absurd hab (not_lt.2 hba.le))
    (pairwise_lt_map_val_toList_univ n) (List.pairwise_lt_finRange n) ?_
  apply (List.perm_ext_iff_of_nodup hnodup (List.nodup_finRange n)).mpr
  intro a
  simp only [List.mem_finRange, iff_true, List.mem_map]
  exact ⟨⟨a, Finset.mem_univ a⟩, FinEnum.mem_toList _, rfl⟩

/-- Variant of `toList_univ_eq_finRange` for the `Fintype` instance coming from `FinEnum`
(`FinEnum.instFintype`), which is the one appearing in the `neighbours_sublist` field of
`WeightedDiGraphWithGenerator` (that structure only has `[FinEnum V]` in scope).  The two
`Fintype (Fin n)` instances are equal since `Fintype` is a subsingleton. -/
theorem toList_univ_finEnum_eq_finRange (n : ℕ) :
    (FinEnum.toList (@Finset.univ (Fin n) FinEnum.instFintype) : List (Fin n)) = List.finRange n := by
  rw [Subsingleton.elim (FinEnum.instFintype) (Fin.fintype n)]
  exact toList_univ_eq_finRange n
