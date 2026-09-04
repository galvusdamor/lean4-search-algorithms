import SearchAlgorithms.ExtractPathFast
import SearchAlgorithms.SearchStepCustom

/-!
# The search drivers with linear-time path reconstruction

`SearchAlgorithms.ExtractPathFast` reconstructs the path to the goal in `O(L)` instead of the
`Θ(L²)` of `WeightedDiGraph.extract_path_to`, and returns *the same path*
(`extract_path_fast_eq`).  This module plugs it into the three drivers of the library:

* `search_exe_fast`                — the generic loop of `SearchAlgorithms.SearchAlgorithm`;
* `search_exe_with_stack_step_fast`— the loop that reads the next node off the queue;
* `search_exe_with_step_eq_fast`   — the loop with a custom (heap) step function.

Each comes with an equation (`search_exe_fast_eq`, `search_exe_with_stack_step_fast_eq`,
`search_exe_with_step_eq_fast_eq`) saying that it returns literally the same
`Option (G.Path start goal)` as the driver it replaces.  Consequently soundness, completeness
and optimality of any search built on these drivers transfer without a new proof: rewrite with
the equation and apply the statement that is already known.
-/

namespace WeightedDiGraph

section

variable {V : Type} {E : Type} [FinEnum V]
variable {G : WeightedDiGraph V E}
variable {D : Type} [FValueComp D]
variable {T : Type} [WellFoundedRelation T]
variable {expandable : V → Prop}
variable {state_type : Type} [has_base_search_state G D state_type]
variable {goal : V}
variable {start : V}
variable {d : D}
variable {start_state : state_type}
variable {search_step : search_step_function G D state_type}
variable {termination_metric : state_type → T}

variable (decreasing_proof : termination_metric_decreasing_proof goal search_step termination_metric)
variable (start_is_base_init : (has_base_search_state.to_base_state (G := G) (D := D) start_state)
    = (base_search_state_initial start d))
variable (invar_carries_over_step : base_invar_carries_over_step search_step (goal := goal)
    (search_invar_all_basic expandable start))

include start_is_base_init invar_carries_over_step

/-- `search_exe` with the linear-time path reconstruction of `extract_path_fast`. -/
def search_exe_fast
    (goal_on_stack_if_terminated : search_step_goal_on_stack_if_terminated
      (search_step := search_step)) :
    Option (G.Path start goal) :=
  let ret := search_internal (start_state := start_state) decreasing_proof
  let final_state := ret.1

  if found_goal_true : ret.2 = true then

    have goal_in_final_visited :=
      search_visited_goal_if_returned_true decreasing_proof start_is_base_init
        invar_carries_over_step goal_on_stack_if_terminated found_goal_true

    have mother_visited := search_returns_with_mother_visited decreasing_proof start_is_base_init
      invar_carries_over_step

    have mother_adjacent := search_returns_with_mother_adjacent decreasing_proof
      start_is_base_init invar_carries_over_step

    have mother_decreasing := search_returns_with_mother_decreasing decreasing_proof
      start_is_base_init invar_carries_over_step

    some (extract_path_fast start goal (has_base_search_state.to_base_state final_state)
      goal_in_final_visited mother_visited mother_adjacent mother_decreasing)
  else
    none

/-- **The fast driver returns the same option as `search_exe`.** -/
theorem search_exe_fast_eq
    (goal_on_stack_if_terminated : search_step_goal_on_stack_if_terminated
      (search_step := search_step)) :
    search_exe_fast (start := start) (d := d) (expandable := expandable) decreasing_proof
        start_is_base_init invar_carries_over_step goal_on_stack_if_terminated
      = search_exe (start := start) (d := d) (expandable := expandable) decreasing_proof
        start_is_base_init invar_carries_over_step goal_on_stack_if_terminated := by
  unfold search_exe_fast search_exe
  simp only [extract_path_fast_eq]

end

section

variable {V : Type} {E : Type} [FinEnum V] [DecidableEq V]
variable {state_type : Type} {D : Type} [FValueComp D] {T : Type} [WellFoundedRelation T]
variable {G : WeightedDiGraph V E} [G.has_base_search_state D state_type]
variable {start : V} {expandable : V → Prop} {d : D}
variable (expand : search_expand G D (state_type := state_type)) (goal : V)
variable {termination_metric : state_type → T} {start_state : state_type}

/-- `search_exe_with_stack_step` with the linear-time path reconstruction. -/
def search_exe_with_stack_step_fast
    (metric_for_expand_proof : termination_proof_for_expand expand goal termination_metric)
    (invar_carries : base_invar_carries_over_expand expand goal
      (search_invar_all_basic expandable start))
    (start_is_base_init : (has_base_search_state.to_base_state (G := G) (D := D) start_state)
      = (base_search_state_initial start d)) :
    Option (G.Path start goal) :=
  let step : search_step_function G D state_type := search_stack_step expand
  let termination_proof : termination_metric_decreasing_proof goal step termination_metric :=
    search_stack_step_reduces_metric expand goal termination_metric metric_for_expand_proof
  let goal_on_stack_if_terminated :
      search_step_goal_on_stack_if_terminated (search_step := step)
        (state_type := state_type) := by
    intro st g
    apply search_stack_step_goal_on_stack_if_terminated
  let base_invars_carry :
      base_invar_carries_over_step step (goal := goal)
        (search_invar_all_basic expandable start) :=
    base_invar_carries_over_stack_step expand goal _ invar_carries
  search_exe_fast (start := start) (goal := goal) (start_state := start_state)
    (search_step := step) (termination_metric := termination_metric) termination_proof
    start_is_base_init base_invars_carry goal_on_stack_if_terminated

/-- **The fast queue driver returns the same option as `search_exe_with_stack_step`.** -/
theorem search_exe_with_stack_step_fast_eq
    (metric_for_expand_proof : termination_proof_for_expand expand goal termination_metric)
    (invar_carries : base_invar_carries_over_expand expand goal
      (search_invar_all_basic expandable start))
    (start_is_base_init : (has_base_search_state.to_base_state (G := G) (D := D) start_state)
      = (base_search_state_initial start d)) :
    search_exe_with_stack_step_fast (start := start) (d := d) (expandable := expandable)
        expand goal metric_for_expand_proof invar_carries start_is_base_init
      = search_exe_with_stack_step (start := start) (d := d) (expandable := expandable)
        (goal := goal) (start_state := start_state) (termination_metric := termination_metric)
        expand metric_for_expand_proof invar_carries start_is_base_init := by
  unfold search_exe_with_stack_step_fast search_exe_with_stack_step
  exact search_exe_fast_eq _ _ _ _

/-- `search_exe_with_step_eq` with the linear-time path reconstruction: a custom (heap) step
function *and* a linear reconstruction of the answer. -/
def search_exe_with_step_eq_fast
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
      search_step_goal_on_stack_if_terminated (search_step := step)
        (state_type := state_type) := by
    rw [hstep]
    intro st g
    apply search_stack_step_goal_on_stack_if_terminated
  let base_invars_carry :
      base_invar_carries_over_step step (goal := goal)
        (search_invar_all_basic expandable start) := by
    rw [hstep]
    exact base_invar_carries_over_stack_step expand goal _ invar_carries
  search_exe_fast (start := start) (goal := goal) (start_state := start_state)
    (search_step := step) (termination_metric := termination_metric) termination_proof
    start_is_base_init base_invars_carry goal_on_stack_if_terminated

/-- **The fast custom-step driver returns the same option as `search_exe_with_step_eq`.** -/
theorem search_exe_with_step_eq_fast_eq
    (step : search_step_function G D state_type)
    (hstep : step = search_stack_step expand)
    (metric_for_expand_proof : termination_proof_for_expand expand goal termination_metric)
    (invar_carries : base_invar_carries_over_expand expand goal
      (search_invar_all_basic expandable start))
    (start_is_base_init : (has_base_search_state.to_base_state (G := G) (D := D) start_state)
      = (base_search_state_initial start d)) :
    search_exe_with_step_eq_fast (start := start) (d := d) (expandable := expandable) expand goal
        step hstep metric_for_expand_proof invar_carries start_is_base_init
      = search_exe_with_step_eq (start := start) (d := d) (expandable := expandable) expand goal
        step hstep metric_for_expand_proof invar_carries start_is_base_init := by
  unfold search_exe_with_step_eq_fast search_exe_with_step_eq
  exact search_exe_fast_eq _ _ _ _

/-- **The fast custom-step driver is the ordinary queue search.**  Composition of
`search_exe_with_step_eq_fast_eq` and `search_exe_with_step_eq_stack`. -/
theorem search_exe_with_step_eq_fast_stack
    (step : search_step_function G D state_type)
    (hstep : step = search_stack_step expand)
    (metric_for_expand_proof : termination_proof_for_expand expand goal termination_metric)
    (invar_carries : base_invar_carries_over_expand expand goal
      (search_invar_all_basic expandable start))
    (start_is_base_init : (has_base_search_state.to_base_state (G := G) (D := D) start_state)
      = (base_search_state_initial start d)) :
    search_exe_with_step_eq_fast (start := start) (d := d) (expandable := expandable) expand goal
        step hstep metric_for_expand_proof invar_carries start_is_base_init
      = search_exe_with_stack_step (start := start) (d := d) (expandable := expandable)
        (goal := goal) (start_state := start_state) (termination_metric := termination_metric)
        expand metric_for_expand_proof invar_carries start_is_base_init := by
  rw [search_exe_with_step_eq_fast_eq]
  exact search_exe_with_step_eq_stack expand goal step hstep metric_for_expand_proof
    invar_carries start_is_base_init

end

end WeightedDiGraph
