import Mathlib.Data.FinEnum
import Mathlib.Data.FinEnum.Option
import Mathlib.Data.Multiset.Defs

variable {V : Type} [FinEnum V] [DecidableEq V]

/-- Compatibility copy of the pre-4.31 subtype enumeration construction.  Mathlib 4.31
marks the corresponding constructors as `implicit_reducible`, which prevents the existing
proofs from unfolding the concrete enumeration. -/
@[reducible] def FinEnum.ofNodupListCompat {α : Type} [DecidableEq α] (xs : List α)
    (h : ∀ x : α, x ∈ xs) (h' : List.Nodup xs) : FinEnum α where
  card := xs.length
  equiv :=
    ⟨fun x => ⟨xs.idxOf x, by rw [List.idxOf_lt_length_iff]; apply h⟩, xs.get,
      fun x => by simp, fun i => by ext; simp [h'.idxOf_getElem]⟩

/-- Compatibility copy of `FinEnum.ofList` with ordinary reducibility. -/
@[reducible] def FinEnum.ofListCompat {α : Type} [DecidableEq α] (xs : List α)
    (h : ∀ x : α, x ∈ xs) : FinEnum α :=
  FinEnum.ofNodupListCompat xs.dedup (by simp [*]) (List.nodup_dedup _)

/-- Compatibility copy of the pre-4.31 subtype enumeration instance. -/
@[reducible] def FinEnum.subtypeCompat {α : Type} [FinEnum α]
    (p : α → Prop) [DecidablePred p] : FinEnum {x // p x} :=
  FinEnum.ofListCompat
    ((FinEnum.toList α).filterMap fun x => if h : p x then some ⟨x, h⟩ else none)
    (by rintro ⟨x, h⟩; simpa)

/-- currently unused. Proof needed to be inlined `in maximum_path_order_of`. -/
theorem FinEnum.empty_to_list_empty_set (states : Finset V):
      (FinEnum.toList { x // x ∈ states }).unattach = [] → states = ∅ := by
  intro toListEmpty
  by_cases h : ∃ x, x ∈ states
  · obtain ⟨s, s_in_states⟩ := h
    have hh : s ∈ (FinEnum.toList { x // x ∈ states }).unattach := by
      clear toListEmpty
      simp_all only [List.mem_unattach, mem_toList, exists_const]
    simp_all
  · simp_all only [not_exists]
    ext a : 1
    simp_all only [Finset.notMem_empty]

theorem finsetLemma (a : Finset W) (b : Finset W): (b ⊆ a) → (a.card = b.card) → (x ∈ a) → x ∈ b := by
  intro b_sub_a same_card x_in_a
  by_contra x_not_in_b
  have b_neq_a : b ≠ a := by
    simp_all only [ne_eq]
    apply Aesop.BuiltinRules.not_intro
    intro a_1
    subst a_1
    simp_all only [not_true_eq_false]
  have b_subset_a : b ⊂ a := by
    apply Finset.ssubset_iff_subset_ne.mpr
    constructor
    exact b_sub_a
    simp_all
  have b_card_le_a_card : b.card < a.card := by
    apply Finset.card_lt_card
    exact b_subset_a
  simp_all only [ne_eq, lt_self_iff_false]

namespace FinEnum

theorem multiset_map_id_attach {α : Type} (a : Multiset α): Multiset.map (fun x => id ↑x) a.attach = a := by
  simp_all only [id_eq, Multiset.attach_map_val]

theorem len_toList {α : Type} [DecidableEq α] [FinEnum α] : (toList (Finset.univ : Finset α)).length = Fintype.card α := by
  rw [← List.toFinset_card_of_nodup]
  · apply Set.BijOn.finsetCard_eq
    rotate_left
    · intro a ; use a
    · simp_all
      conv =>
        left
        arg 1
        ext x
        rw [← id_eq (a := x.val)]
      apply multiset_map_id_attach
  · simp

end FinEnum

instance [FinEnum V] : FinEnum (Option V) := FinEnum.instFinEnumOptionLast V
