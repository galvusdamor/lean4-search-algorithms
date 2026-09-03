import SearchAlgorithms.SearchStep

/-!
# Running the search with a custom step function

The generic search loop of `SearchAlgorithms.SearchStep` reads the next node to expand off
the *abstract* state:

```
search_stack_step expand goal s =
  match (to_base_state s).stack with
  | [] => (s, some false)
  | head :: tail => if head = goal then (s, some true) else (expand s head tail, none)
```

For every state representation so far this is free, because the representation *stores* the
queue as a list.  A state whose queue is a heap does not: its abstract queue is the sorted
list of the heap entries, and building it costs `O(m log m)` — which would have to be paid
in *every* iteration, defeating the purpose of the heap.

Such an implementation therefore needs a step function of its own, one that pops the heap
instead of looking at `(to_base_state s).stack`.  This file provides the corresponding
driver: `search_exe_with_step_eq` runs `search_exe` with a step function `step` given
together with a proof that it *is* `search_stack_step expand` — the equation is discharged
once and for all from the invariants of the state representation, and
`search_exe_with_step_eq_stack` then says that the run is the very same one as
`search_exe_with_stack_step`.  So no correctness statement has to be re-proved: everything
that is known about `search_exe_with_stack_step` applies verbatim.
-/

namespace WeightedDiGraph

section

variable {V E : Type} [FinEnum V] [DecidableEq V]
variable {state_type : Type} {D : Type} [FValueComp D] {T : Type} [WellFoundedRelation T]
variable {G : WeightedDiGraph V E} [G.has_base_search_state D state_type]
variable {start : V} {expandable : V → Prop} {d : D}
variable (expand : search_expand G D (state_type := state_type)) (goal : V)
variable {termination_metric : state_type → T} {start_state : state_type}

/-- The search of `search_exe_with_stack_step`, but executed with the step function `step`,
which is only required to be *equal* to `search_stack_step expand`.

The point is that `step` may compute the next node to expand in a completely different (and
much cheaper) way, as long as the outcome is the same; the equation `hstep` is a `Prop` and
hence erased at run time. -/
def search_exe_with_step_eq
    (step : search_step_function G D state_type)
    (hstep : step = search_stack_step expand)
    (metric_for_expand_proof : termination_proof_for_expand expand goal termination_metric)
    (invar_carries : base_invar_carries_over_expand expand goal
      (search_invar_all_basic expandable start))
    (start_is_base_init : (has_base_search_state.to_base_state (G := G) (D := D) start_state)
      = (base_search_state_initial start d)) :
    Option (G.Path start goal) :=
  let termination_proof : termination_metric_decreasing_proof goal step termination_metric := by
    rw [hstep]
    exact search_stack_step_reduces_metric expand goal termination_metric metric_for_expand_proof
  let goal_on_stack_if_terminated :
      search_step_goal_on_stack_if_terminated (search_step := step) (state_type := state_type) := by
    rw [hstep]
    intro st g
    apply search_stack_step_goal_on_stack_if_terminated
  let base_invars_carry :
      base_invar_carries_over_step step (goal := goal) (search_invar_all_basic expandable start) := by
    rw [hstep]
    exact base_invar_carries_over_stack_step expand goal _ invar_carries
  search_exe (start := start) (goal := goal) (start_state := start_state) (search_step := step)
    (termination_metric := termination_metric) termination_proof start_is_base_init
    base_invars_carry goal_on_stack_if_terminated

/-- **The custom-step search is the ordinary search.**  Both sides only differ in *how* the
next node is found, and `hstep` says that the outcome is the same; the remaining arguments
are proofs, so the two runs are literally the same term. -/
theorem search_exe_with_step_eq_stack
    (step : search_step_function G D state_type)
    (hstep : step = search_stack_step expand)
    (metric_for_expand_proof : termination_proof_for_expand expand goal termination_metric)
    (invar_carries : base_invar_carries_over_expand expand goal
      (search_invar_all_basic expandable start))
    (start_is_base_init : (has_base_search_state.to_base_state (G := G) (D := D) start_state)
      = (base_search_state_initial start d)) :
    search_exe_with_step_eq (start := start) (d := d) (expandable := expandable) expand goal step
        hstep metric_for_expand_proof invar_carries start_is_base_init
      = search_exe_with_stack_step (start := start) (d := d) (expandable := expandable)
        (goal := goal) (start_state := start_state) (termination_metric := termination_metric)
        expand metric_for_expand_proof invar_carries start_is_base_init := by
  subst hstep
  rfl

end

end WeightedDiGraph
