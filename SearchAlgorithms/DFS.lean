import Graphlib.SearchStep

-- def local global variable for a graph
variable {V : Type} {E : Type} [FinEnum V] [DecidableEq V]
variable {g : WeightedDiGraph V E}


namespace WeightedDiGraph
-----------------------------------------------------------------------
------ DFS implementation and proof ------

def dfs_step_expand[FinEnum V] [DecidableEq V]
    (g: WeightedDiGraph V E)
    (priorState : base_search_state g ℕ)
    (stackHead : V)
    (stackTail : List V):
    (base_search_state g ℕ) :=
      let newly_visited : Finset V := (Finset.univ).filterMap
        (λ v => if @decide (g.Adj stackHead v) (g.instDecAdj stackHead v) ∧ v ∉ priorState.visited
                  then some v
                  else none)
        (by intro a a' b a_1 a_2; simp_all) -- filter neighbors to expand the visited list

      let vList : List V := (FinEnum.toList (Finset.univ : Finset V))
      let newly_visited_list : List V :=
        vList.filterMap (λ v => if v ∈ newly_visited then some v else none)
      let new_visited : Finset V := priorState.visited ∪ newly_visited
      let new_stack : List V := newly_visited_list ++ stackTail -- add neighbors in front to stack

      let new_mother : new_visited → V := fun ⟨v, hv⟩  =>
        if h: (v ∈ priorState.visited) then priorState.mother ⟨ v, by exact h⟩
        else stackHead

      let new_order : V → Nat := fun v  =>
        if h: (v ∈ priorState.visited) then priorState.pathOrder v
        else if hh : (priorState.visited.card = 0) then 0
        --else 1 + maximum_path_order_of g priorState priorState.visited (by simp_all)
        else 1 + priorState.pathOrder stackHead
        -- priorState.stack.length

      base_search_state.mk new_visited new_order new_mother new_stack


lemma dfs_expand_newly_added_are_adjacent
    (priorState : base_search_state g ℕ)
    (stackHead : V)
    (stackTail : List V):
    ∀ x : V, x ∉ priorState.visited ∧ x ∉ stackTail ∧
      x ∈ (dfs_step_expand g priorState stackHead stackTail).stack →
      g.Adj stackHead x := by
    intro x ⟨x_not_visi, ⟨ x_not_on_stack_before, x_on_stack_after ⟩  ⟩
    unfold dfs_step_expand at x_on_stack_after
    simp_all


lemma dfs_expand_keeps_stack_in_visited
    (priorState : base_search_state g ℕ)
    (stackHead : V)
    (stackTail : List V):
    search_invar_stack_is_visited priorState ∧
      stackHead ∈ priorState.visited ∧ (∀ x : V, x ∉ priorState.visited → x ∉ stackTail) →
      search_invar_stack_is_visited (dfs_step_expand g priorState stackHead stackTail) := by
      intro ⟨ stack_is_visited_prior, stackhead_visited, x_not_in_stack_tail⟩
      unfold search_invar_stack_is_visited
      intro x x_now_on_stack
      unfold dfs_step_expand
      simp_all
      by_cases x_was_visited : x ∈ priorState.visited
      · left
        exact x_was_visited
      · right
        apply And.intro
        · apply (dfs_expand_newly_added_are_adjacent priorState stackHead stackTail)
          simp_all
        · exact x_was_visited


lemma dfs_expand_keeps_mother_in_visited
    (priorState : base_search_state g ℕ)
    (stackHead : V)
    (stackTail : List V):
    search_invar_mother_is_visited priorState ∧ stackHead ∈ priorState.visited → search_invar_mother_is_visited (dfs_step_expand g priorState stackHead stackTail) := by
      intro mother_is_visited_prior
      unfold search_invar_mother_is_visited
      intro x
      simp_all
      unfold dfs_step_expand
      simp_all
      by_cases x_is_already_visited : ↑x ∈ priorState.visited
      all_goals
        simp_all

lemma dfs_expand_keeps_mother_is_adjacent
    (start : V)
    (priorState : base_search_state g ℕ)
    (stackHead : V)
    (stackTail : List V):
    search_invar_mother_is_adjacent start priorState → search_invar_mother_is_adjacent start (dfs_step_expand g priorState stackHead stackTail) := by
      intro mother_is_adjacent_prior
      unfold search_invar_mother_is_adjacent
      intro x
      simp_all
      intro x_not_start
      unfold dfs_step_expand
      simp_all
      split
      · simp_all
      · next x_not_prior_visited =>
        obtain ⟨ xx, x_in_new_visited ⟩ := x
        unfold dfs_step_expand at x_in_new_visited
        simp at x_in_new_visited
        simp_all

lemma dfs_expand_keeps_mother_ordered
    (start : V)
    (priorState : base_search_state g ℕ)
    (stackHead : V)
    (stackTail : List V):
    search_invar_mother_is_visited priorState ∧
      stackHead ∈ priorState.visited ∧
      search_invar_mother_decreasing_path_order start priorState
      → search_invar_mother_decreasing_path_order start
          (dfs_step_expand g priorState stackHead stackTail)
          := by
    intro ⟨mother_is_visited, stack_head_visited_prior,mother_decreasing_prior⟩
    unfold search_invar_mother_decreasing_path_order
    intro a a_not_stat
    unfold dfs_step_expand
    simp_all
    split
    · next a_visited =>
      simp_all
    · next a_not_visited =>
      split
      · simp_all
      · rw [Nat.add_comm]
        unfold FValueComp.lt
        unfold Nat.instFValueComp
        simp

lemma dfs_expand_keeps_on_stack_or_all_neighbours_visited
    (priorState : base_search_state g ℕ)
    (stackHead : V)
    (stackTail : List V):
     search_invar_on_stack_or_all_neighbours_visited priorState
     ∧ priorState.stack = (stackHead :: stackTail)
     → search_invar_on_stack_or_all_neighbours_visited
          (dfs_step_expand g priorState stackHead stackTail)
          := by
      intro ⟨ invar_holds_on_prior_state, stack_composition ⟩
      unfold search_invar_on_stack_or_all_neighbours_visited
      intro ⟨ x, x_now_on_stack⟩
      by_cases x_not_stack_head : x ≠ stackHead
      · by_cases x_was_not_in_stack_tail_: x ∈ stackTail
        · left
          unfold dfs_step_expand
          simp_all
        · by_cases x_not_visited : x ∉ priorState.visited
          · left
            unfold dfs_step_expand
            unfold dfs_step_expand at x_now_on_stack
            simp at x_now_on_stack
            simp_all
          · simp_all -- x was visited before and is not on the stack any more
            right
            intro y x_adj_y
            unfold dfs_step_expand
            simp_all
            left
            have x_invar := invar_holds_on_prior_state x
            simp_all
      · simp_all
        right
        intro y x_adj_y
        unfold dfs_step_expand
        simp_all
        by_cases h : y ∈ priorState.visited
        · left; exact h
        · right; exact h

lemma dfs_expand_keeps_start_visited
    (start : V)
    (priorState : base_search_state g ℕ)
    (stackHead : V)
    (stackTail : List V):
     search_invar_start_visited start priorState →
     search_invar_start_visited start (dfs_step_expand g priorState stackHead stackTail)
          := by
      intro pre_invar
      unfold dfs_step_expand
      unfold search_invar_start_visited
      simp_all

lemma dfs_expand_visited_subset (priorState : base_search_state g ℕ)
    (stackHead : V)
    (stackTail : List V):
    priorState.visited ⊆ (dfs_step_expand g priorState stackHead stackTail).visited := by
    unfold dfs_step_expand
    simp_all

lemma dfs_expand_keeps_goal_on_stack :
    base_invar_carries_over_expand (state_type := base_search_state g ℕ) (dfs_step_expand g) goal (search_prop_goal_on_stack (G:=g) (D:=ℕ) goal):= by
    unfold base_invar_carries_over_expand
    intro s head tail ⟨ goal_prior_on_stack, head_not_goal, compose⟩
    change search_prop_goal_on_stack goal (dfs_step_expand g s head tail)
    unfold dfs_step_expand
    unfold search_prop_goal_on_stack at ⊢ goal_prior_on_stack
    simp_all
    cases  goal_prior_on_stack
    all_goals
      simp_all

lemma dfs_expand_goal_becomes_visited_puts_it_on_stack
  (goal : V)
  :
  goal_becomes_visited_puts_it_on_stack (G:=g) (D:=ℕ) (dfs_step_expand g) goal:= by
    unfold goal_becomes_visited_puts_it_on_stack
    intro s head tail ⟨ a,b,c,d⟩
    change search_prop_goal_on_stack goal (dfs_step_expand g s head tail)
    have bb : goal ∈ (dfs_step_expand g s head tail).visited := b
    clear b
    unfold dfs_step_expand at bb ⊢
    unfold search_prop_goal_on_stack
    simp_all
    cases bb
    · contradiction
    · next h => left; exact h




lemma dfs_expand_visited_increases
    (priorState : base_search_state g ℕ)
    (head : V)
    (tail : List V):
      (dfs_step_expand g priorState head tail).visited.card ≥ priorState.visited.card := by
    change priorState.visited.card ≤ (dfs_step_expand g priorState head tail).visited.card
    apply Finset.card_le_card
    apply dfs_expand_visited_subset


lemma dfs_expand_keeps_base_invars:
  base_invar_carries_over_expand (dfs_step_expand g) goal (search_invar_all_basic (G:=g) (D:=ℕ) start) := by
  unfold base_invar_carries_over_expand
  unfold search_invar_all_basic
  intro s head tail ⟨ ⟨ i1,i2,i3,i4,i5,i6⟩ , head_not_goal, compose⟩
  have head_is_visited : head ∈ s.visited := by
    apply i1
    rw [compose]
    simp
  and_intros
  · apply dfs_expand_keeps_stack_in_visited
    constructor
    · exact i1
    · constructor
      · exact head_is_visited
      · intro x x_not_visited
        by_contra x_in_tail
        have x_on_stack : x ∈ (has_base_search_state.to_base_state (G:=g) (D:=ℕ) s).stack := by
          rw [compose]
          simp_all
        apply i1 at x_on_stack
        contradiction
  · apply dfs_expand_keeps_mother_in_visited
    constructor
    · exact i2
    · exact head_is_visited
  · apply dfs_expand_keeps_mother_is_adjacent
    exact i3
  · apply dfs_expand_keeps_mother_ordered
    constructor
    · exact i2
    · constructor
      · exact head_is_visited
      · exact i4
  · apply dfs_expand_keeps_on_stack_or_all_neighbours_visited
    constructor
    · exact i5
    · exact compose
  · apply dfs_expand_keeps_start_visited
    exact i6

--------------------------------------------------------------------------------------------------
-- main recursion loop

lemma termination_dfs_recurse
    (priorState : base_search_state g ℕ)
    (nextState : base_search_state g ℕ)
    (head : V)
    (tail : List V)
    (compose : priorState.stack = head :: tail):
    (nextState = (dfs_step_expand g priorState head tail))
    → ((Fintype.card V - nextState.visited.card < Fintype.card V - priorState.visited.card
        ∨ (Fintype.card V - nextState.visited.card = Fintype.card V - priorState.visited.card ∧ nextState.stack.length < priorState.stack.length)) ):= by
  intro nextStateDef
  apply (Classical.or_iff_not_imp_left).mpr
  intro visited_not_decreasing
  simp_all
  have same_visited : (dfs_step_expand g priorState head tail).visited.card = priorState.visited.card := by
    have k2 : (dfs_step_expand g priorState head tail).visited.card ≤ Fintype.card V := by
      apply visited_is_smaller_than_V
    have k3 : (dfs_step_expand g priorState head tail).visited.card ≥ priorState.visited.card := by
      apply dfs_expand_visited_increases
    omega
  have visited_eq : priorState.visited = (dfs_step_expand g priorState head tail).visited := by
    ext a
    constructor
    · apply Finset.mem_of_subset
      apply dfs_expand_visited_subset
    apply finsetLemma
    · apply dfs_expand_visited_subset
    exact same_visited

  constructor
  · omega
  · unfold dfs_step_expand
    simp_all
    simp [Nat.add_comm]
    intro a head_adj_a
    rw [visited_eq]
    unfold dfs_step_expand
    simp_all
    classical
    by_cases h : a ∈ (dfs_step_expand g priorState head tail).visited
    · left; exact h
    · right; exact h

lemma dfs_expand_metric_reduction : termination_proof_for_expand (G:=g) (D:=ℕ) (dfs_step_expand g) goal base_search_state_termination_metric := by
    unfold termination_proof_for_expand
    unfold base_search_state_termination_metric
    simp
    intro s head tail head_not_goal stack_not_empty

    unfold WellFoundedRelation.rel
    unfold Prod.instWellFoundedRelation
    apply Prod.lex_iff.mpr
    simp
    apply termination_dfs_recurse
    · exact stack_not_empty
    · rfl


----------------- the actual DFS: create the initial search state and then recurse

def dfs (g: WeightedDiGraph V E) (start : V) (goal : V): Option (g.Path start goal) :=
  let start_state : base_search_state g ℕ := base_search_state_initial start 0
  have h : has_base_search_state.to_base_state (G:=g) start_state = base_search_state_initial start 0:= by
    simp_all only [start_state]; rfl

  search_exe_with_stack_step (G:=g) (start := start) (dfs_step_expand g) goal dfs_expand_metric_reduction dfs_expand_keeps_base_invars h


theorem dfs_is_sound (g: WeightedDiGraph V E) (start : V) (goal : V) :
    (Option.isSome (dfs g start goal) → (∃ x : (g.Path start goal), x = x)) := by
  unfold dfs
  apply search_with_stack_step_is_sound



theorem dfs_is_complete (g: WeightedDiGraph V E) (start : V) (goal : V):
    ((∃ x : (g.Path start goal), x = x) → Option.isSome (dfs g start goal)) := by
  unfold dfs
  apply search_with_stack_step_is_complete
  · apply dfs_expand_keeps_goal_on_stack
  · apply dfs_expand_goal_becomes_visited_puts_it_on_stack

end WeightedDiGraph
