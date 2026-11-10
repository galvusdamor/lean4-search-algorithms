import SearchAlgorithms.SearchSimStack

/-!
# Simulation along a relation

`SearchAlgorithms.SearchSimStack` transfers a search along a *function* from one state type to
the other.  When the faster representation does not determine the slower one (a bucket queue
does not determine the shape of a heap with the same entries), the two can still be related:
if related states have the same abstract state and expanding related states gives related
states, the two searches return the same result (`search_exe_with_stack_step_sim_rel`).
-/

namespace WeightedDiGraph

section

variable {V E : Type} [FinEnum V] [DecidableEq V]
variable {G : WeightedDiGraph V E}
variable {D : Type} [FValueComp D]
variable {A B : Type} [G.has_base_search_state D A] [G.has_base_search_state D B]
variable {goal : V}

theorem search_recurse_sim_rel
    {T T' : Type} [WellFoundedRelation T] [WellFoundedRelation T']
    (R : A → B → Prop)
    (stepA : search_step_function G D A) (stepB : search_step_function G D B)
    (hstep : ∀ (g : V) (a : A) (b : B), R a b →
      R (stepA g a).1 (stepB g b).1 ∧ (stepA g a).2 = (stepB g b).2)
    (mA : A → T) (dpA : termination_metric_decreasing_proof goal stepA mA)
    (mB : B → T') (dpB : termination_metric_decreasing_proof goal stepB mB) :
    ∀ (a : A) (b : B), R a b →
      R (search_recurse (goal := goal) a stepA mA dpA).1
          (search_recurse (goal := goal) b stepB mB dpB).1 ∧
        (search_recurse (goal := goal) a stepA mA dpA).2
          = (search_recurse (goal := goal) b stepB mB dpB).2 := by
  have hwf : WellFounded (fun x y : A => WellFoundedRelation.rel (mA x) (mA y)) :=
    InvImage.wf mA WellFoundedRelation.wf
  intro a
  induction a using hwf.induction with
  | _ a ih =>
    intro b hab
    rw [search_recurse_eq a stepA mA dpA, search_recurse_eq b stepB mB dpB]
    obtain ⟨h1, h2⟩ := hstep goal a b hab
    by_cases hnone : (stepA goal a).2 = none
    · have hnone' : (stepB goal b).2 = none := h2 ▸ hnone
      rw [dif_pos hnone, dif_pos hnone']
      exact ih _ (dpA a hnone) _ h1
    · have hnone' : ¬ (stepB goal b).2 = none := h2 ▸ hnone
      rw [dif_neg hnone, dif_neg hnone']
      refine ⟨h1, ?_⟩
      simp only
      congr 1

theorem search_stack_step_sim_rel
    (R : A → B → Prop)
    (hto : ∀ a b, R a b → has_base_search_state.to_base_state (G := G) (D := D) a
      = has_base_search_state.to_base_state (G := G) (D := D) b)
    (eA : search_expand G D (state_type := A)) (eB : search_expand G D (state_type := B))
    (hexp : ∀ (a : A) (b : B) (head : V) (tail : List V), R a b →
      (has_base_search_state.to_base_state (G := G) (D := D) a).stack = head :: tail →
      R (eA a head tail) (eB b head tail))
    (a : A) (b : B) (hab : R a b) :
    R (search_stack_step eA goal a).1 (search_stack_step eB goal b).1 ∧
      (search_stack_step eA goal a).2 = (search_stack_step eB goal b).2 := by
  unfold search_stack_step
  have hb := hto a b hab
  simp only [← hb]
  cases h : (has_base_search_state.to_base_state (G := G) (D := D) a).stack with
  | nil => exact ⟨hab, rfl⟩
  | cons x xs =>
    by_cases hx : x = goal
    · simp only [hx, if_true]; exact ⟨hab, trivial⟩
    · simp only [hx, if_false]; exact ⟨hexp a b x xs hab h, trivial⟩

variable {T T' : Type} [WellFoundedRelation T] [WellFoundedRelation T']
variable {start : V} {expandable : V → Prop} {d : D}

/-- **Transfer along a relation.**  Related start states, related expansions and equal
abstract states of related states give the same search result. -/
theorem search_exe_with_stack_step_sim_rel
    (R : A → B → Prop)
    (hto : ∀ a b, R a b → has_base_search_state.to_base_state (G := G) (D := D) a
      = has_base_search_state.to_base_state (G := G) (D := D) b)
    (eA : search_expand G D (state_type := A)) (eB : search_expand G D (state_type := B))
    (hexp : ∀ (a : A) (b : B) (head : V) (tail : List V), R a b →
      (has_base_search_state.to_base_state (G := G) (D := D) a).stack = head :: tail →
      R (eA a head tail) (eB b head tail))
    {sA : A} {sB : B} (hst : R sA sB)
    (mA : A → T) (mB : B → T')
    (mpA : termination_proof_for_expand eA goal mA)
    (icA : base_invar_carries_over_expand eA goal (search_invar_all_basic expandable start))
    (hA : (has_base_search_state.to_base_state (G := G) (D := D) sA)
      = base_search_state_initial start d)
    (mpB : termination_proof_for_expand eB goal mB)
    (icB : base_invar_carries_over_expand eB goal (search_invar_all_basic expandable start))
    (hB : (has_base_search_state.to_base_state (G := G) (D := D) sB)
      = base_search_state_initial start d) :
    search_exe_with_stack_step (start := start) (d := d) (expandable := expandable) (goal := goal)
        (start_state := sA) (termination_metric := mA) eA mpA icA hA
      = search_exe_with_stack_step (start := start) (d := d) (expandable := expandable)
        (goal := goal) (start_state := sB) (termination_metric := mB) eB mpB icB hB := by
  have hsim := search_recurse_sim_rel (G := G) (D := D) (goal := goal) R
    (search_stack_step eA) (search_stack_step eB)
    (fun g a b h => search_stack_step_sim_rel (goal := g) R hto eA eB hexp a b h)
    mA (search_stack_step_reduces_metric eA goal mA mpA)
    mB (search_stack_step_reduces_metric eB goal mB mpB) sA sB hst
  unfold search_exe_with_stack_step search_exe search_internal
  obtain ⟨h1, h2⟩ := hsim
  simp only
  split
  · next hf =>
    split
    · apply congrArg some
      apply Subtype.ext
      apply extract_path_to_state_congr
      exact hto _ _ h1
    · next hf' => exact absurd (h2 ▸ hf) hf'
  · next hf =>
    split
    · next hf' => exact absurd (h2 ▸ hf') hf
    · rfl

end

end WeightedDiGraph
