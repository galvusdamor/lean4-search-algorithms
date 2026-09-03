import SearchAlgorithms.SearchStep

/-!
# Simulation between two representations of the search state

The generic search of `SearchAlgorithms.SearchAlgorithm` /
`SearchAlgorithms.SearchStep` is parametric in the *concrete* type `state_type` used to
represent a search state; the only thing it requires is an abstraction function
`has_base_search_state.to_base_state : state_type → base_search_state G D` into the
mathematical (`Finset`/function based) state on which all correctness statements are
phrased.

This file exploits that parametricity.  Assume two state representations `A` and `B`
together with

* a translation `φ : A → B` that *preserves the abstract state*
  (`to_base_state (φ a) = to_base_state a`), and
* expansion functions `eA`, `eB` that *commute* with `φ`
  (`φ (eA a head tail) = eB (φ a) head tail`),

then the whole search returns the very same result for both representations
(`search_exe_with_stack_step_sim`).

This is the tool used to transfer soundness, completeness and optimality from the
reference implementation to an implementation that stores its state in efficient
(flattened) data structures: it suffices to show that one expansion step produces the
same *abstract* state, no matter how that state is encoded.
-/

namespace WeightedDiGraph

section

variable {V E : Type} [FinEnum V] [DecidableEq V]
variable {G : WeightedDiGraph V E}
variable {D : Type} [FValueComp D]
variable {A B : Type} [G.has_base_search_state D A] [G.has_base_search_state D B]
variable {goal : V}

omit [DecidableEq V] in
/-- One-step unfolding equation of `search_recurse`. -/
theorem search_recurse_eq {T : Type} [WellFoundedRelation T]
    (priorState : A) (step : search_step_function G D A) (m : A → T)
    (dp : termination_metric_decreasing_proof goal step m) :
    search_recurse (goal := goal) priorState step m dp
      = if h : (step goal priorState).2 = none then
          search_recurse (goal := goal) (step goal priorState).1 step m dp
        else ((step goal priorState).1,
          (step goal priorState).2.get (Option.isSome_iff_ne_none.mpr h)) := by
  rw [search_recurse]

omit [DecidableEq V] in
/-- One step of the recursion simulates the other: if the concrete step functions commute
with the translation `φ`, then so does the whole recursion `search_recurse` — including the
returned boolean. -/
theorem search_recurse_sim
    {T T' : Type} [WellFoundedRelation T] [WellFoundedRelation T']
    (phi : A → B)
    (stepA : search_step_function G D A) (stepB : search_step_function G D B)
    (hstep : ∀ (g : V) (a : A), stepB g (phi a) = (phi (stepA g a).1, (stepA g a).2))
    (mA : A → T) (dpA : termination_metric_decreasing_proof goal stepA mA)
    (mB : B → T') (dpB : termination_metric_decreasing_proof goal stepB mB)
    (a : A) :
    search_recurse (goal := goal) (phi a) stepB mB dpB
      = (phi (search_recurse (goal := goal) a stepA mA dpA).1,
         (search_recurse (goal := goal) a stepA mA dpA).2) := by
  have hwf : WellFounded (fun x y : A => WellFoundedRelation.rel (mA x) (mA y)) :=
    InvImage.wf mA WellFoundedRelation.wf
  induction a using hwf.induction with
  | _ a ih =>
    rw [search_recurse_eq (phi a) stepB mB dpB, search_recurse_eq a stepA mA dpA]
    simp only [hstep]
    by_cases hnone : (stepA goal a).2 = none
    · simp only [hnone, dif_pos]
      exact ih _ (dpA a hnone)
    · simp only [hnone, dif_neg, not_false_iff]

/-- The stack-based step commutes with a translation that preserves the abstract state and
commutes with the expansion. -/
theorem search_stack_step_sim
    (phi : A → B)
    (hto : ∀ a : A, has_base_search_state.to_base_state (G := G) (D := D) (phi a)
      = has_base_search_state.to_base_state (G := G) (D := D) a)
    (eA : search_expand G D (state_type := A)) (eB : search_expand G D (state_type := B))
    (hexp : ∀ (a : A) (head : V) (tail : List V), phi (eA a head tail) = eB (phi a) head tail)
    (a : A) :
    search_stack_step eB goal (phi a)
      = (phi (search_stack_step eA goal a).1, (search_stack_step eA goal a).2) := by
  unfold search_stack_step
  simp only [hto]
  cases h : (has_base_search_state.to_base_state (G := G) (D := D) a).stack with
  | nil => simp
  | cons x xs =>
    by_cases hx : x = goal
    · simp [hx]
    · simp [hx, hexp]

end

section

variable {V E : Type} [FinEnum V] [DecidableEq V]
variable {G : WeightedDiGraph V E}
variable {D : Type} [FValueComp D]
variable {A B : Type} [G.has_base_search_state D A] [G.has_base_search_state D B]
variable {T T' : Type} [WellFoundedRelation T] [WellFoundedRelation T']
variable {goal start : V} {expandable : V → Prop} {d : D}

/-- **Transfer theorem.**  Two implementations of the same search that only differ in *how*
the search state is represented return the same path.

The hypotheses are exactly the two facts one has to check for a new state representation:
`phi` translates the initial state and preserves the abstract state (`hto`), and one
expansion step produces the same (translated) state (`hexp`). -/
theorem search_exe_with_stack_step_sim
    (phi : A → B)
    (hto : ∀ a : A, has_base_search_state.to_base_state (G := G) (D := D) (phi a)
      = has_base_search_state.to_base_state (G := G) (D := D) a)
    (eA : search_expand G D (state_type := A)) (eB : search_expand G D (state_type := B))
    (hexp : ∀ (a : A) (head : V) (tail : List V), phi (eA a head tail) = eB (phi a) head tail)
    {sA : A}
    (mA : A → T) (mB : B → T')
    (mpA : termination_proof_for_expand eA goal mA)
    (icA : base_invar_carries_over_expand eA goal (search_invar_all_basic expandable start))
    (hA : (has_base_search_state.to_base_state (G := G) (D := D) sA)
      = base_search_state_initial start d)
    (mpB : termination_proof_for_expand eB goal mB)
    (icB : base_invar_carries_over_expand eB goal (search_invar_all_basic expandable start))
    (hB : (has_base_search_state.to_base_state (G := G) (D := D) (phi sA))
      = base_search_state_initial start d) :
    search_exe_with_stack_step (start := start) (d := d) (expandable := expandable) (goal := goal)
        (start_state := phi sA) (termination_metric := mB) eB mpB icB hB
      = search_exe_with_stack_step (start := start) (d := d) (expandable := expandable)
        (goal := goal) (start_state := sA) (termination_metric := mA) eA mpA icA hA := by
  have hsim := search_recurse_sim (G := G) (D := D) (goal := goal) phi
    (search_stack_step eA) (search_stack_step eB)
    (fun g a => search_stack_step_sim (goal := g) phi hto eA eB hexp a)
    mA (search_stack_step_reduces_metric eA goal mA mpA)
    mB (search_stack_step_reduces_metric eB goal mB mpB) sA
  unfold search_exe_with_stack_step search_exe search_internal
  simp only [hsim]
  split
  · apply congrArg some
    apply Subtype.ext
    apply extract_path_to_state_congr
    rw [hsim]
    exact hto _
  · rfl

/-- Variant of `search_exe_with_stack_step_sim` in which the start state of the second
implementation is only *equal* to the translated start state of the first one (rather than
literally being it). -/
theorem search_exe_with_stack_step_sim'
    (phi : A → B)
    (hto : ∀ a : A, has_base_search_state.to_base_state (G := G) (D := D) (phi a)
      = has_base_search_state.to_base_state (G := G) (D := D) a)
    (eA : search_expand G D (state_type := A)) (eB : search_expand G D (state_type := B))
    (hexp : ∀ (a : A) (head : V) (tail : List V), phi (eA a head tail) = eB (phi a) head tail)
    {sA : A} {sB : B} (hstart : phi sA = sB)
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
        (start_state := sB) (termination_metric := mB) eB mpB icB hB
      = search_exe_with_stack_step (start := start) (d := d) (expandable := expandable)
        (goal := goal) (start_state := sA) (termination_metric := mA) eA mpA icA hA := by
  subst hstart
  exact search_exe_with_stack_step_sim phi hto eA eB hexp mA mB mpA icA hA mpB icB hB

end

end WeightedDiGraph
