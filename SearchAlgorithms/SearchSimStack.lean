import SearchAlgorithms.SearchSim

/-!
# Simulation for state representations that rely on the queue invariant

`SearchAlgorithms.SearchSim` transfers a search from one state representation to another
provided the expansion functions commute with the translation **for every** `head` and
`tail`:

```
hexp : ∀ a head tail, phi (eA a head tail) = eB (phi a) head tail
```

An implementation that *maintains* the search queue in sorted order (instead of re-sorting
it after every expansion, see `SearchAlgorithms.HeuristicSearchSorted`) only reproduces the
reference behaviour when `head :: tail` really is the queue of the state it is applied to —
which is exactly how the search loop calls it.  The theorems below are the corresponding
transfer results with the weaker hypothesis

```
hexp : ∀ a head tail, (to_base_state a).stack = head :: tail →
         phi (eA a head tail) = eB (phi a) head tail
```

The proofs are the ones of `SearchAlgorithms.SearchSim`; only the point where `hexp` is used
changes, and there the `stack = head :: tail` equation is available from the case split of
`search_stack_step`.

Note that the other two obligations of the search driver, `termination_proof_for_expand` and
`base_invar_carries_over_expand`, already carry the `stack = head :: tail` hypothesis.
-/

namespace WeightedDiGraph

section

variable {V E : Type} [FinEnum V] [DecidableEq V]
variable {G : WeightedDiGraph V E}
variable {D : Type} [FValueComp D]
variable {A B : Type} [G.has_base_search_state D A] [G.has_base_search_state D B]
variable {goal : V}

/-- Variant of `search_stack_step_sim` in which the expansion functions only have to agree
on the actual queue of the state. -/
theorem search_stack_step_sim_of_stack
    (phi : A → B)
    (hto : ∀ a : A, has_base_search_state.to_base_state (G := G) (D := D) (phi a)
      = has_base_search_state.to_base_state (G := G) (D := D) a)
    (eA : search_expand G D (state_type := A)) (eB : search_expand G D (state_type := B))
    (hexp : ∀ (a : A) (head : V) (tail : List V),
      (has_base_search_state.to_base_state (G := G) (D := D) a).stack = head :: tail →
      phi (eA a head tail) = eB (phi a) head tail)
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
    · simp [hx, hexp a x xs h]

end

section

variable {V E : Type} [FinEnum V] [DecidableEq V]
variable {G : WeightedDiGraph V E}
variable {D : Type} [FValueComp D]
variable {A B : Type} [G.has_base_search_state D A] [G.has_base_search_state D B]
variable {T T' : Type} [WellFoundedRelation T] [WellFoundedRelation T']
variable {goal start : V} {expandable : V → Prop} {d : D}

/-- **Transfer theorem for queue-invariant implementations.**  Same as
`search_exe_with_stack_step_sim`, but the expansion functions only have to agree when
`head :: tail` is the queue of the state. -/
theorem search_exe_with_stack_step_sim_of_stack
    (phi : A → B)
    (hto : ∀ a : A, has_base_search_state.to_base_state (G := G) (D := D) (phi a)
      = has_base_search_state.to_base_state (G := G) (D := D) a)
    (eA : search_expand G D (state_type := A)) (eB : search_expand G D (state_type := B))
    (hexp : ∀ (a : A) (head : V) (tail : List V),
      (has_base_search_state.to_base_state (G := G) (D := D) a).stack = head :: tail →
      phi (eA a head tail) = eB (phi a) head tail)
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
    (fun g a => search_stack_step_sim_of_stack (goal := g) phi hto eA eB hexp a)
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

/-- Variant of `search_exe_with_stack_step_sim_of_stack` in which the start state of the
second implementation is only *equal* to the translated start state of the first one. -/
theorem search_exe_with_stack_step_sim_of_stack'
    (phi : A → B)
    (hto : ∀ a : A, has_base_search_state.to_base_state (G := G) (D := D) (phi a)
      = has_base_search_state.to_base_state (G := G) (D := D) a)
    (eA : search_expand G D (state_type := A)) (eB : search_expand G D (state_type := B))
    (hexp : ∀ (a : A) (head : V) (tail : List V),
      (has_base_search_state.to_base_state (G := G) (D := D) a).stack = head :: tail →
      phi (eA a head tail) = eB (phi a) head tail)
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
  exact search_exe_with_stack_step_sim_of_stack phi hto eA eB hexp mA mB mpA icA hA mpB icB hB

end

end WeightedDiGraph
