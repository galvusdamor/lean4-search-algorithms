import Graphlib.SearchAlgorithm


section


namespace WeightedDiGraph

-- def local global variable for a graph
variable {V : Type} {E : Type} [FinEnum V] [DecidableEq V]
abbrev search_expand (G : WeightedDiGraph V E) (D : Type) [FValueComp D]
  {state_type : Type} [has_base_search_state G D state_type] : Type :=
    state_type → V → List V → state_type



section
variable {state_type : Type}
variable {D : Type} [FValueComp D]
variable {T : Type} [WellFoundedRelation T]
variable {G : WeightedDiGraph V E}
variable {start : V}
variable [G.has_base_search_state D state_type]

section
variable (expand : search_expand G D (state_type := state_type))
variable (goal : V)
--variable {prior_state : state_type}

def search_stack_step
  (prior_state : state_type):
  state_type × (Option Bool) :=
  let s := (has_base_search_state.to_base_state (G:=G) (D:=D) prior_state)

  match s.stack with
    | [] => (prior_state, some false) -- goal not found
    | (s :: xs) =>
      if s = goal then (prior_state, some true)
      else (expand prior_state s xs, none)


lemma search_stack_step_goal_on_stack_if_terminated (priorState : state_type):
    (search_stack_step expand goal priorState).2 = some true →
     goal ∈ (has_base_search_state.to_base_state (G:=G) (D:=D) (search_stack_step expand goal priorState).1).stack := by
   intro terminated_with_true
   next step_did_terminate =>
   unfold search_stack_step at terminated_with_true ⊢
   simp
   split
   · next l stack_empty =>
     simp_all
   · next l head tail stack_not_empty =>
     simp_all
     split
     all_goals
      simp_all


lemma search_stack_step_goal_stack_head_if_terminated
  (priorState : state_type)
  :
    (search_stack_step expand goal priorState).2 = some true →
  (has_base_search_state.to_base_state (G:=G) (D:=D) (search_stack_step expand goal priorState).1).stack.head? = some goal := by
   intro terminated_with_true
   next step_did_terminate =>
   unfold search_stack_step at terminated_with_true ⊢
   simp
   split
   · next l stack_empty =>
     simp_all
   · next l head tail stack_not_empty =>
     simp_all
     split
     all_goals
      simp_all


abbrev base_invar_carries_over_expand
    (invar : base_search_state G D → Prop) :=
      ∀ s : state_type, ∀ head : V, ∀ tail : List V,
        invar (has_base_search_state.to_base_state s)
          ∧ ¬ head = goal
          ∧ (has_base_search_state.to_base_state (G:=G) (D:=D) s).stack = head :: tail
        → invar (has_base_search_state.to_base_state (expand s head tail))



lemma base_invar_carries_over_stack_step
    (invar : base_search_state G D → Prop)
    (invar_carries : base_invar_carries_over_expand expand goal invar):
  base_invar_carries_over_step (goal:=goal) (search_stack_step expand) invar := by
  unfold base_invar_carries_over_step
  intro s invar_holds_for_s
  unfold search_stack_step
  simp
  split
  · exact invar_holds_for_s
  · split
    · exact invar_holds_for_s
    · next head tail compose head_not_goal=>
      apply invar_carries
      and_intros
      · exact invar_holds_for_s
      · exact head_not_goal
      · exact compose


lemma stack_step_stack_empty_if_terminated_without_goal
    (priorState : state_type):
    (search_stack_step expand goal priorState).2 = false →
     (has_base_search_state.to_base_state (G:=G) (D:=D) (search_stack_step expand goal priorState).1).stack = [] := by
   intro terminated_with_true
   next step_did_terminate =>
   unfold search_stack_step at terminated_with_true ⊢
   simp
   split
   · next l stack_empty =>
     simp_all
   · next l head tail stack_not_empty =>
     simp_all
     split
     all_goals
      simp_all




lemma stack_step_keeps_goal_on_stack
    (priorState : state_type)
    (goal_on_stack_carries_expand : base_invar_carries_over_expand expand goal (search_prop_goal_on_stack goal)):
    search_prop_goal_on_stack goal (has_base_search_state.to_base_state (G:=G) (D:=D) priorState) →
    search_prop_goal_on_stack goal (has_base_search_state.to_base_state (G:=G) (D:=D) (search_stack_step expand goal priorState).1) := by
      unfold search_prop_goal_on_stack
      intro goal_prior_on_stack
      unfold search_stack_step
      simp
      split
      · simp_all
      · split
        · simp_all
        · next head tail compose head_not_goal =>
          apply goal_on_stack_carries_expand
          constructor
          · apply goal_prior_on_stack
          · exact ⟨ head_not_goal, compose ⟩


lemma stack_step_terminates_when_goal_stack_head
    (priorState : state_type)
    :
    (∃ tail : List V, (has_base_search_state.to_base_state (G:=G) (D:=D) priorState).stack = goal :: tail) →
    (search_stack_step expand goal priorState).2 = some true := by
      intro ⟨ tail, goal_head ⟩
      unfold search_stack_step
      simp_all


abbrev goal_becomes_visited_puts_it_on_stack
    :=
      ∀ s : state_type, ∀ head : V, ∀ tail : List V,
            goal ∉ (has_base_search_state.to_base_state (G:=G) (D:=D) s).visited
          ∧ goal ∈ (has_base_search_state.to_base_state (G:=G) (D:=D) (expand s head tail)).visited
          ∧ ¬ head = goal
          ∧ (has_base_search_state.to_base_state (G:=G) (D:=D) s).stack = head :: tail
        → search_prop_goal_on_stack goal (has_base_search_state.to_base_state (G:=G) (D:=D) (expand s head tail))




lemma stack_step_goal_becomes_visited_it_is_on_stack
    (priorState : state_type)
    (goal_trigger : goal_becomes_visited_puts_it_on_stack expand goal)
  :
    goal ∉ (has_base_search_state.to_base_state (G:=G) (D:=D) priorState).visited
  ∧ goal ∈ (has_base_search_state.to_base_state (G:=G) (D:=D) (search_stack_step expand goal priorState).1).visited
  → search_prop_goal_on_stack goal (has_base_search_state.to_base_state (G:=G) (D:=D) (search_stack_step expand goal priorState).1)
    := by
  intro ⟨ goal_was_not_visited, goal_now_visited ⟩
  unfold search_stack_step at goal_now_visited ⊢
  dsimp
  split
  · simp_all
  · simp_all ; split <;> simp_all



--------------------------
-- Actual search algorithm

section
--variable {expand : search_expand g (state_type := state_type)}
variable {termination_metric : state_type → T}
variable {start_state : state_type}
variable {d : D}

abbrev termination_proof_for_expand
    (termination_metric : state_type → T):=
    ∀ state : state_type, ∀ head : V, ∀ tail : List V,
      head ≠ goal ∧ (has_base_search_state.to_base_state (G:=G) (D:=D) state).stack = head :: tail
    → WellFoundedRelation.rel (termination_metric (expand state head tail)) (termination_metric state)
    --(termination_metric (expand state head tail)).1 < (termination_metric state).1 ∨
    --  (termination_metric (expand state head tail)).1 = (termination_metric state).1 ∧
    --    (termination_metric (expand state head tail)).2 < (termination_metric state).2

lemma search_stack_step_reduces_metric
  (termination_metric : state_type → T)
  (termination_dfs_recurse : termination_proof_for_expand expand goal termination_metric)
  :
    ∀ s : state_type, (search_stack_step expand goal s).2 = none →
        WellFoundedRelation.rel
        (termination_metric (search_stack_step expand goal s).1) (termination_metric s) := by
    intro state did_not_terminate

    unfold search_stack_step at did_not_terminate
    simp_all

    have h : ¬search_prop_stack_empty (has_base_search_state.to_base_state (G:=G) (D:=D) state) := by
      unfold search_prop_stack_empty
      split at did_not_terminate
      all_goals
        simp_all

    unfold search_prop_stack_empty at h
    apply List.length_pos_iff_ne_nil.mpr at h
    obtain ⟨ head, tail, compose ⟩ := List.exists_of_length_succ (n:=(has_base_search_state.to_base_state (G:=G) (D:=D) state).stack.length - 1) (has_base_search_state.to_base_state (G:=G) (D:=D) state).stack (by omega)

    unfold search_stack_step
    simp_all
    split
    · simp_all
    · apply termination_dfs_recurse
      · constructor
        · split at did_not_terminate
          · simp_all
          · simp_all
        · exact compose

section

def search_exe_with_stack_step
    (metric_for_expand_proof : termination_proof_for_expand expand goal termination_metric)
    (invar_carries : base_invar_carries_over_expand expand goal (search_invar_all_basic start))
    (start_is_base_init : (has_base_search_state.to_base_state (G:=G) (D:=D) start_state) = (base_search_state_initial start d))
    :
    Option (G.Path start goal) :=
    let step : search_step_function G D state_type := search_stack_step expand
    let termination_proof : termination_metric_decreasing_proof goal step termination_metric :=
      search_stack_step_reduces_metric expand goal termination_metric metric_for_expand_proof

    let goal_on_stack_if_terminated : search_step_goal_on_stack_if_terminated (search_step:=step) (state_type := state_type):= by
      unfold search_step_goal_on_stack_if_terminated
      intro st goal
      apply search_stack_step_goal_on_stack_if_terminated

    let base_invars_carry : base_invar_carries_over_step step (search_invar_all_basic start) := by
      apply base_invar_carries_over_stack_step
      exact invar_carries

    search_exe (start := start) (goal:=goal) (start_state:=start_state) (search_step:=step) (termination_metric := termination_metric) (termination_proof) start_is_base_init base_invars_carry goal_on_stack_if_terminated


-- function needed for proofs
def search_with_stack_step
    (metric_for_expand_proof : termination_proof_for_expand expand goal termination_metric)
    :
    state_type × Bool:=

    let step : search_step_function G D state_type := search_stack_step expand
    let termination_proof : termination_metric_decreasing_proof goal step termination_metric :=
      search_stack_step_reduces_metric expand goal termination_metric metric_for_expand_proof

    search_internal (goal:=goal) (start_state:=start_state) (search_step:=step) (termination_metric := termination_metric) (termination_proof)



theorem search_with_stack_step_is_sound
    (metric_for_expand_proof : termination_proof_for_expand expand goal termination_metric)
    (invar_carries : base_invar_carries_over_expand expand goal (search_invar_all_basic start))
    (start_is_base_init : (has_base_search_state.to_base_state (G:=G) (D:=D) start_state) = (base_search_state_initial start d))
    :
    (Option.isSome (search_exe_with_stack_step expand goal metric_for_expand_proof invar_carries start_is_base_init) → (∃ x : (G.Path start goal), x = x)) := by
  intro h -- Option.isSome true on some and false on none, x = x since we need a formula
  unfold search_exe_with_stack_step at h
  simp at h
  apply search_is_sound (state_type := state_type) (D:=D) (T:=T)
  apply h



theorem search_with_stack_step_is_complete
    (metric_for_expand_proof : termination_proof_for_expand expand goal termination_metric)
    (invar_carries : base_invar_carries_over_expand expand goal (search_invar_all_basic start))
    (start_is_base_init : (has_base_search_state.to_base_state (G:=G) (D:=D) start_state) = (base_search_state_initial start d))
    (goal_on_stack_carries_expand : base_invar_carries_over_expand expand goal (search_prop_goal_on_stack goal))
    (goal_trigger : goal_becomes_visited_puts_it_on_stack expand goal)
    :
    ((∃ x : (G.Path start goal), x = x) → Option.isSome (search_exe_with_stack_step expand goal metric_for_expand_proof invar_carries start_is_base_init)) := by
    intro path
    unfold search_exe_with_stack_step
    simp
    apply search_is_complete
    · apply stack_step_stack_empty_if_terminated_without_goal
    · unfold step_keeps_goal_on_stack
      intro s
      apply stack_step_keeps_goal_on_stack
      apply goal_on_stack_carries_expand
    · unfold step_goal_becomes_visited_it_is_on_stack
      intro s
      apply stack_step_goal_becomes_visited_it_is_on_stack
      apply goal_trigger
    · apply stack_step_terminates_when_goal_stack_head
    · exact path

end

end

end

end

end WeightedDiGraph

end
