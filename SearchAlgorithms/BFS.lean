import Graphlib.SearchStep

-- def local global variable for a graph
variable {V : Type} {E : Type} [FinEnum V] [DecidableEq V]
variable {g : WeightedDiGraph V E}


namespace WeightedDiGraph
-----------------------------------------------------------------------
------ BFS implementation and proof ------

def bfs_step_expand[FinEnum V] [DecidableEq V]
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
      let new_stack : List V := stackTail ++ newly_visited_list -- add neighbors at end of stack

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


lemma bfs_expand_newly_added_are_adjacent
    (priorState : base_search_state g ℕ)
    (stackHead : V)
    (stackTail : List V):
    ∀ x : V, x ∉ priorState.visited ∧ x ∉ stackTail ∧
      x ∈ (bfs_step_expand g priorState stackHead stackTail).stack →
      g.Adj stackHead x := by
    intro x ⟨x_not_visi, ⟨ x_not_on_stack_before, x_on_stack_after ⟩  ⟩
    unfold bfs_step_expand at x_on_stack_after
    simp_all


lemma bfs_expand_keeps_stack_in_visited
    (priorState : base_search_state g ℕ)
    (stackHead : V)
    (stackTail : List V):
    search_invar_stack_is_visited priorState ∧
      stackHead ∈ priorState.visited ∧ (∀ x : V, x ∉ priorState.visited → x ∉ stackTail) →
      search_invar_stack_is_visited (bfs_step_expand g priorState stackHead stackTail) := by
      intro ⟨ stack_is_visited_prior, stackhead_visited, x_not_in_stack_tail⟩
      unfold search_invar_stack_is_visited
      intro x x_now_on_stack
      unfold bfs_step_expand
      simp_all
      by_cases x_was_visited : x ∈ priorState.visited
      · left
        exact x_was_visited
      · right
        apply And.intro
        · apply (bfs_expand_newly_added_are_adjacent priorState stackHead stackTail)
          simp_all
        · exact x_was_visited


lemma bfs_expand_keeps_mother_in_visited
    (priorState : base_search_state g ℕ)
    (stackHead : V)
    (stackTail : List V):
    search_invar_mother_is_visited priorState ∧ stackHead ∈ priorState.visited → search_invar_mother_is_visited (bfs_step_expand g priorState stackHead stackTail) := by
      intro mother_is_visited_prior
      unfold search_invar_mother_is_visited
      intro x
      simp_all
      unfold bfs_step_expand
      simp_all
      by_cases x_is_already_visited : ↑x ∈ priorState.visited
      all_goals
        simp_all

lemma bfs_expand_keeps_mother_is_adjacent
    (start : V)
    (priorState : base_search_state g ℕ)
    (stackHead : V)
    (stackTail : List V):
    search_invar_mother_is_adjacent start priorState → search_invar_mother_is_adjacent start (bfs_step_expand g priorState stackHead stackTail) := by
      intro mother_is_adjacent_prior
      unfold search_invar_mother_is_adjacent
      intro x
      simp_all
      intro x_not_start
      unfold bfs_step_expand
      simp_all
      split
      · simp_all
      · next x_not_prior_visited =>
        obtain ⟨ xx, x_in_new_visited ⟩ := x
        unfold bfs_step_expand at x_in_new_visited
        simp at x_in_new_visited
        simp_all

lemma bfs_expand_keeps_mother_ordered
    (start : V)
    (priorState : base_search_state g ℕ)
    (stackHead : V)
    (stackTail : List V):
    search_invar_mother_is_visited priorState ∧
      stackHead ∈ priorState.visited ∧
      search_invar_mother_decreasing_path_order start priorState
      → search_invar_mother_decreasing_path_order start
          (bfs_step_expand g priorState stackHead stackTail)
          := by
    intro ⟨mother_is_visited, stack_head_visited_prior,mother_decreasing_prior⟩
    unfold search_invar_mother_decreasing_path_order
    intro a a_not_stat
    unfold bfs_step_expand
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

lemma bfs_expand_keeps_on_stack_or_all_neighbours_visited
    (priorState : base_search_state g ℕ)
    (stackHead : V)
    (stackTail : List V):
     search_invar_on_stack_or_all_neighbours_visited priorState
     ∧ priorState.stack = (stackHead :: stackTail)
     → search_invar_on_stack_or_all_neighbours_visited
          (bfs_step_expand g priorState stackHead stackTail)
          := by
      intro ⟨ invar_holds_on_prior_state, stack_composition ⟩
      unfold search_invar_on_stack_or_all_neighbours_visited
      intro ⟨ x, x_now_on_stack⟩
      by_cases x_not_stack_head : x ≠ stackHead
      · by_cases x_was_not_in_stack_tail_: x ∈ stackTail
        · left
          unfold bfs_step_expand
          simp_all
        · by_cases x_not_visited : x ∉ priorState.visited
          · left
            unfold bfs_step_expand
            unfold bfs_step_expand at x_now_on_stack
            simp at x_now_on_stack
            simp_all
          · simp_all -- x was visited before and is not on the stack any more
            right
            intro y x_adj_y
            unfold bfs_step_expand
            simp_all
            left
            have x_invar := invar_holds_on_prior_state x
            simp_all
      · simp_all
        right
        intro y x_adj_y
        unfold bfs_step_expand
        simp_all
        by_cases h : y ∈ priorState.visited
        · left; exact h
        · right; exact h

lemma bfs_expand_keeps_start_visited
    (start : V)
    (priorState : base_search_state g ℕ)
    (stackHead : V)
    (stackTail : List V):
     search_invar_start_visited start priorState →
     search_invar_start_visited start (bfs_step_expand g priorState stackHead stackTail)
          := by
      intro pre_invar
      unfold bfs_step_expand
      unfold search_invar_start_visited
      simp_all

lemma bfs_expand_visited_subset (priorState : base_search_state g ℕ)
    (stackHead : V)
    (stackTail : List V):
    priorState.visited ⊆ (bfs_step_expand g priorState stackHead stackTail).visited := by
    unfold bfs_step_expand
    simp_all

lemma bfs_expand_keeps_goal_on_stack :
    base_invar_carries_over_expand (state_type := base_search_state g ℕ) (bfs_step_expand g) goal (search_prop_goal_on_stack (G:=g) (D:=ℕ) goal):= by
    unfold base_invar_carries_over_expand
    intro s head tail ⟨ goal_prior_on_stack, head_not_goal, compose⟩
    change search_prop_goal_on_stack goal (bfs_step_expand g s head tail)
    unfold bfs_step_expand
    unfold search_prop_goal_on_stack at ⊢ goal_prior_on_stack
    simp_all
    cases  goal_prior_on_stack
    all_goals
      simp_all

lemma bfs_expand_goal_becomes_visited_puts_it_on_stack
  (goal : V)
  :
  goal_becomes_visited_puts_it_on_stack (G:=g) (D:=ℕ) (bfs_step_expand g) goal:= by
    unfold goal_becomes_visited_puts_it_on_stack
    intro s head tail ⟨ a,b,c,d⟩
    change search_prop_goal_on_stack goal (bfs_step_expand g s head tail)
    have bb : goal ∈ (bfs_step_expand g s head tail).visited := b
    clear b
    unfold bfs_step_expand at bb ⊢
    unfold search_prop_goal_on_stack
    simp_all
    cases bb
    · contradiction
    · next h => right; exact h


lemma bfs_expand_visited_increases
    (priorState : base_search_state g ℕ)
    (head : V)
    (tail : List V):
      (bfs_step_expand g priorState head tail).visited.card ≥ priorState.visited.card := by
    change priorState.visited.card ≤ (bfs_step_expand g priorState head tail).visited.card
    apply Finset.card_le_card
    apply bfs_expand_visited_subset


lemma bfs_expand_keeps_base_invars:
  base_invar_carries_over_expand (bfs_step_expand g) goal (search_invar_all_basic (G:=g) (D:=ℕ) start) := by
  unfold base_invar_carries_over_expand
  unfold search_invar_all_basic
  intro s head tail ⟨ ⟨ i1,i2,i3,i4,i5,i6⟩ , head_not_goal, compose⟩
  have head_is_visited : head ∈ s.visited := by
    apply i1
    rw [compose]
    simp
  and_intros
  · apply bfs_expand_keeps_stack_in_visited
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
  · apply bfs_expand_keeps_mother_in_visited
    constructor
    · exact i2
    · exact head_is_visited
  · apply bfs_expand_keeps_mother_is_adjacent
    exact i3
  · apply bfs_expand_keeps_mother_ordered
    constructor
    · exact i2
    · constructor
      · exact head_is_visited
      · exact i4
  · apply bfs_expand_keeps_on_stack_or_all_neighbours_visited
    constructor
    · exact i5
    · exact compose
  · apply bfs_expand_keeps_start_visited
    exact i6

--------------------------------------------------------------------------------------------------
-- main recursion loop

lemma termination_bfs_recurse
    (priorState : base_search_state g ℕ)
    (nextState : base_search_state g ℕ)
    (head : V)
    (tail : List V)
    (compose : priorState.stack = head :: tail):
    (nextState = (bfs_step_expand g priorState head tail))
    → ((Fintype.card V - nextState.visited.card < Fintype.card V - priorState.visited.card
        ∨ (Fintype.card V - nextState.visited.card = Fintype.card V - priorState.visited.card ∧ nextState.stack.length < priorState.stack.length)) ):= by
  intro nextStateDef
  apply (Classical.or_iff_not_imp_left).mpr
  intro visited_not_decreasing
  simp_all
  have same_visited : (bfs_step_expand g priorState head tail).visited.card = priorState.visited.card := by
    have k2 : (bfs_step_expand g priorState head tail).visited.card ≤ Fintype.card V := by
      apply visited_is_smaller_than_V
    have k3 : (bfs_step_expand g priorState head tail).visited.card ≥ priorState.visited.card := by
      apply bfs_expand_visited_increases
    omega
  have visited_eq : priorState.visited = (bfs_step_expand g priorState head tail).visited := by
    ext a
    constructor
    · apply Finset.mem_of_subset
      apply bfs_expand_visited_subset
    apply finsetLemma
    · apply bfs_expand_visited_subset
    exact same_visited

  constructor
  · omega
  · unfold bfs_step_expand
    simp_all
    intro a head_adj_a
    unfold bfs_step_expand
    simp_all
    classical
    by_cases h : a ∈ (bfs_step_expand g priorState head tail).visited
    · left; exact h
    · right; exact h

lemma bfs_expand_metric_reduction : termination_proof_for_expand (G:=g) (D:=ℕ) (bfs_step_expand g) goal base_search_state_termination_metric := by
    unfold termination_proof_for_expand
    unfold base_search_state_termination_metric
    simp
    intro s head tail head_not_goal stack_not_empty
    unfold WellFoundedRelation.rel
    unfold Prod.instWellFoundedRelation
    apply Prod.lex_iff.mpr
    simp
    apply termination_bfs_recurse
    · exact stack_not_empty
    · rfl


----------------- the actual bfs: create the initial search state and then recurse

def bfs(g: WeightedDiGraph V E) (start : V) (goal : V): Option (g.Path start goal) :=
  let start_state := base_search_state_initial start 0
  have h : has_base_search_state.to_base_state (G:=g) start_state = base_search_state_initial start 0:= by simp_all only [start_state]; rfl

  search_exe_with_stack_step (G:=g) (start := start) (bfs_step_expand g) goal bfs_expand_metric_reduction bfs_expand_keeps_base_invars h


def bfs_last_state (g: WeightedDiGraph V E) (start : V) (goal : V): base_search_state g ℕ × Bool :=
  search_with_stack_step (goal:=goal) (start_state := base_search_state_initial start 0) (bfs_step_expand g) bfs_expand_metric_reduction


theorem bfs_is_sound (g: WeightedDiGraph V E) (start : V) (goal : V) :
    (Option.isSome (bfs g start goal) → (∃ x : (g.Path start goal), x = x)) := by
  apply search_with_stack_step_is_sound
  · apply bfs_expand_metric_reduction
  · apply bfs_expand_keeps_base_invars
  · rfl



theorem bfs_is_complete (g: WeightedDiGraph V E) (start : V) (goal : V):
    ((∃ x : (g.Path start goal), x = x) → Option.isSome (bfs g start goal)) := by
  apply search_with_stack_step_is_complete
  · apply bfs_expand_metric_reduction
  · apply bfs_expand_keeps_base_invars
  · rfl
  · apply bfs_expand_keeps_goal_on_stack
  · apply bfs_expand_goal_becomes_visited_puts_it_on_stack



-------------


abbrev bfs_invar_on_stack_or_all_neighbours_max_order (s : base_search_state g ℕ):=
  ∀ x : s.visited, ↑x ∉ s.stack → ∀ y : V, (g.Adj x y) → s.pathOrder y ≤ 1 + s.pathOrder x


abbrev bfs_path_as_extracted_as_long_as_sort_index (start : V) (s : base_search_state g ℕ) :=
    ∀ mother_invar : search_invar_mother_is_visited s,
    ∀ mother_invar_adj : search_invar_mother_is_adjacent start s,
    ∀ decreasing_invar : search_invar_mother_decreasing_path_order start s,
    ∀ u : V, ∀ h : u ∈ s.visited,
    (extract_path_to start u s h mother_invar mother_invar_adj decreasing_invar).1.length = s.pathOrder u

-- stack is sorted by the path_order (i.e. distance) value
abbrev bfs_stack_sorted (s : base_search_state g ℕ) :=
  List.Pairwise (fun u v => s.pathOrder u ≤ s.pathOrder v) s.stack

-- for BFS we don't sort the stack, we just append
-- this is allowed as the maximum difference of values in the stack is one (from head to tail)
abbrev bfs_stack_max_diff (s : base_search_state g ℕ) :=
  if stack_not_empty : s.stack ≠ [] then
    ∀ x ∈ s.stack, s.pathOrder (s.stack.head stack_not_empty) + 1 ≥ s.pathOrder x
  else true


-- this invariant is only true for BFS and Dijkstra
-- for A*, we might have to re-open
abbrev bfs_stack_shortest_path (start : V) (s : base_search_state g ℕ) :=
  ∀ u ∈ s.visited, u ∉ s.stack ∨ (if ne : s.stack ≠ [] then s.stack.head ne = u else false) → g.distance_is start u (s.pathOrder u)


-- for A*, a node that is not on the stack might have a shortert path that goes through some node that is actually still on the stack
-- this is due to inconsistent heuristics requiring re-opening
-- TODO here we need a "splicing lemma" for paths that states that in these cases the
abbrev astar_stack_shortest_path (start : V) (s : base_search_state g ℕ) :=
  ∀ u ∈ s.visited, u ∉ s.stack ∨ (if ne : s.stack ≠ [] then s.stack.head ne = u else false) → (g.distance_is start u (s.pathOrder u) ∨ (
    ∀ p : g.Path start u, p.is_shortest → p.support ∩ s.stack ≠ ∅
  ))


abbrev bfs_all_invar (start : V) (s : base_search_state g ℕ) :=
      search_invar_all_basic start s
    ∧ bfs_stack_shortest_path start s
    ∧ bfs_path_as_extracted_as_long_as_sort_index start s
    ∧ bfs_invar_on_stack_or_all_neighbours_max_order s
    ∧ bfs_stack_sorted s
    ∧ bfs_stack_max_diff s
    ∧ search_invar_start_path_order_zero start s



lemma order_u_le_walk_length_p (start u v : V)
  (p : g.Walk start v)
  (state : base_search_state g ℕ)
  (update_invar : bfs_invar_on_stack_or_all_neighbours_max_order state)
  (on_stack_or_nei_visited : search_invar_on_stack_or_all_neighbours_visited state)
  (start_visited : start ∈ state.visited)
  (u_in_support : u ∈ p.support)
  (u_on_stack : u ∈ state.stack)
  (all_prior_not_on_stack : (p.support.takeWhile (· ≠ u)).all (· ∉ state.stack))
  (u_ne_v : u ≠ v)
  :
    state.pathOrder u - state.pathOrder start < p.length := by
      -- by induction and using the expansion invar
      -- must be strictly smaller as u is not the last node on the path!
      cases p
      case nil =>
        apply Walk.mem_support_nil_iff.mp at u_in_support
        contradiction
      case cons w h p' =>
        unfold Walk.length
        by_cases u_eq_start : u = start
        · grind
        · have u_in_new_supp : u ∈ p'.support := by
            apply Walk.cons_support at u_in_support
            cases u_in_support <;> simp_all

          have start_not_on_stack  : start ∉ state.stack := by
            unfold List.takeWhile at all_prior_not_on_stack
            unfold Walk.support at all_prior_not_on_stack
            simp  at all_prior_not_on_stack
            split at all_prior_not_on_stack <;> simp_all

          have w_visited : w ∈ state.visited := by
            specialize on_stack_or_nei_visited ⟨start,start_visited⟩
            grind
          have all_p'_prior_not_on_stack : (p'.support.takeWhile (· ≠ u)).all (· ∉ state.stack) := by
            unfold Walk.support at all_prior_not_on_stack
            simp at all_prior_not_on_stack
            unfold List.takeWhile at all_prior_not_on_stack
            split at all_prior_not_on_stack <;> simp_all
          have via_recursion := order_u_le_walk_length_p w u v p' state update_invar on_stack_or_nei_visited w_visited u_in_new_supp u_on_stack all_p'_prior_not_on_stack u_ne_v

          specialize update_invar ⟨ start, start_visited ⟩ start_not_on_stack w h
          simp_all
          omega

lemma order_u_le_path_length_p (start u v : V)
  (p : g.Path start v)
  (state : base_search_state g ℕ)
  (update_invar : bfs_invar_on_stack_or_all_neighbours_max_order state)
  (on_stack_or_nei_visited : search_invar_on_stack_or_all_neighbours_visited state)
  (start_path_order : search_invar_start_path_order_zero start state)
  (start_visited : search_invar_start_visited start state)
  (u_in_support : u ∈ p.support)
  (u_on_stack : u ∈ state.stack)
  (all_prior_not_on_stack : (p.support.takeWhile (· ≠ u)).all (· ∉ state.stack))
  (u_ne_v : u ≠ v)
  :
    -- todo: also need that all nodes *before* in the support are not on stack!
    state.pathOrder u < p.length := by
      have h := order_u_le_walk_length_p start u v p.val state update_invar on_stack_or_nei_visited start_visited u_in_support u_on_stack all_prior_not_on_stack u_ne_v
      simp_all


lemma bfs_expand_does_not_change_paths (start u : V) (s : base_search_state g ℕ):
    ∀ mother_invar : search_invar_mother_is_visited s,
    ∀ mother_invar_adj : search_invar_mother_is_adjacent start s,
    ∀ decreasing_invar : search_invar_mother_decreasing_path_order start s,
    ∀ mother_invar' : search_invar_mother_is_visited (bfs_step_expand g s head tail),
    ∀ mother_invar_adj' : search_invar_mother_is_adjacent start (bfs_step_expand g s head tail),
    ∀ decreasing_invar' : search_invar_mother_decreasing_path_order start (bfs_step_expand g s head tail),
    ∀ h : u ∈ s.visited, ∀ h' : u ∈ (bfs_step_expand g s head tail).visited,
      (extract_path_to start u s h mother_invar mother_invar_adj decreasing_invar).fst.val.length =
      (extract_path_to start u (bfs_step_expand g s head tail) h' mother_invar' mother_invar_adj'
          decreasing_invar').fst.val.length := by
      intro mother_invar mother_invar_adj decreasing_invar mother_invar' mother_invar_adj' decreasing_invar' u_visited u_visited'
      unfold extract_path_to
      simp
      split
      · simp
      · unfold Path.concat
        dsimp only
        repeat rw [Walk.concat_inc_length_by_one]
        apply Nat.add_left_cancel_iff.mpr
        have hh : ((bfs_step_expand g s head tail).mother ⟨u, u_visited'⟩) = (s.mother ⟨u, u_visited⟩) := by
          simp_all [bfs_step_expand]
        rw [extract_path_visited_proof_irrelevant (u_eq_v := hh)]
        apply bfs_expand_does_not_change_paths
        unfold bfs_step_expand
        simp
        left
        simp_all
termination_by FValueComp.wf.wrap (s.pathOrder u)
decreasing_by
  apply decreasing_invar
  simp_all



lemma bfs_expand_start_path_order_zero_carries (start : V) (goal : V)
    (state : base_search_state g ℕ)
    (start_visited : search_invar_start_visited start state)
    :
     ∀ head : V, ∀ tail : List V,
        search_invar_start_path_order_zero start state
          ∧ ¬ head = goal
          ∧ state.stack = head :: tail
        → search_invar_start_path_order_zero start (bfs_step_expand g state head tail) := by
      --unfold base_invar_carries_over_expand
      intro head tail ⟨ prior_invar,head_ne_goal,compose⟩
      --unfold has_base_search_state.to_base_state
      --unfold instHas_base_search_stateBase_search_state
      unfold search_invar_start_path_order_zero
      unfold bfs_step_expand
      simp_all

lemma bfs_expand_keeps_extracted_same_length_as_sort_index (start : V) (goal : V)
    (state : base_search_state g ℕ)
    (start_visited : search_invar_start_visited start state)
    (bef_mother_invar : search_invar_mother_is_visited state)
    (bef_mother_invar_adj : search_invar_mother_is_adjacent start state)
    (bef_decreasing_invar : search_invar_mother_decreasing_path_order start state)
    (bef_stack_visited_invar : search_invar_stack_is_visited state)
    :
     ∀ head : V, ∀ tail : List V,
        bfs_path_as_extracted_as_long_as_sort_index start state
          ∧ ¬ head = goal
          ∧ state.stack = head :: tail
        → bfs_path_as_extracted_as_long_as_sort_index start (bfs_step_expand g state head tail) := by
      --unfold base_invar_carries_over_expand
      intro head tail ⟨ prior_invar,head_ne_goal,compose⟩
      --unfold has_base_search_state.to_base_state
      --unfold instHas_base_search_stateBase_search_state
      --simp
      unfold bfs_path_as_extracted_as_long_as_sort_index
      --unfold bfs_step_expand
      intro mother_invar mother_invar_adj decreasing_invar u h
      unfold Path.length
      by_cases u_visited_before : u ∈ state.visited
      · rw [← bfs_expand_does_not_change_paths]
        rotate_left
        · exact bef_mother_invar
        · exact bef_mother_invar_adj
        · exact bef_decreasing_invar
        · exact u_visited_before
        · simp_all [bfs_step_expand, bfs_path_as_extracted_as_long_as_sort_index]
      · have head_visited : head ∈ state.visited := by
          apply bef_stack_visited_invar
          simp_all
        have head_visited_after : head ∈ (bfs_step_expand g state head tail).visited := by
          unfold bfs_step_expand
          simp_all

        have qq : (extract_path_to start u (bfs_step_expand g state head tail) h mother_invar mother_invar_adj decreasing_invar).fst.val.length = 1 + (extract_path_to start head (bfs_step_expand g state head tail) head_visited_after mother_invar mother_invar_adj decreasing_invar).fst.val.length := by
          conv =>
              left
              unfold extract_path_to
          simp
          split
          · next u_is_start =>
            unfold search_invar_start_visited at start_visited
            simp_all
          · next u_ne_start =>
            unfold Path.concat
            rw [Walk.concat_inc_length_by_one]
            apply Nat.add_left_cancel_iff.mpr
            apply extract_path_visited_proof_irrelevant
            unfold bfs_step_expand
            simp
            intro u_visited
            contradiction

        have qqq : (bfs_step_expand g state head tail).pathOrder u = 1 + (bfs_step_expand g state head tail).pathOrder head := by
          unfold bfs_step_expand
          simp
          split_ifs <;> simp_all

        have qqqq : (bfs_step_expand g state head tail).pathOrder head = state.pathOrder head := by
          unfold bfs_step_expand
          simp
          intro head_not_visited
          contradiction

        have qqqqq : (extract_path_to start head (bfs_step_expand g state head tail) head_visited_after mother_invar mother_invar_adj decreasing_invar).fst.val.length = (extract_path_to start head state head_visited bef_mother_invar bef_mother_invar_adj bef_decreasing_invar).fst.val.length := by
          rw [← bfs_expand_does_not_change_paths]

        rw [qq]
        rw [qqq]
        rw [qqqqq]
        rw [qqqq]
        apply Nat.add_left_cancel_iff.mpr
        apply prior_invar

lemma bfs_expand_keeps_max_diff (goal : V)
    (state : base_search_state g ℕ)
    (bef_stack_visited_invar : search_invar_stack_is_visited state)
    (stack_sorted : bfs_stack_sorted state)
    :
     ∀ head : V, ∀ tail : List V,
        bfs_stack_max_diff state
          ∧ ¬ head = goal
          ∧ state.stack = head :: tail
        → bfs_stack_max_diff (bfs_step_expand g state head tail) := by
      intro head tail ⟨ prior_invar, head_ne_goal, compose ⟩
      unfold bfs_stack_max_diff at prior_invar ⊢

      have head_in_stack : head ∈ state.stack := by simp_all
      have head_in_visited : head ∈ state.visited := by simp_all
      have visi_ne_nil : state.visited ≠ ∅ := by intro visi_empty ; simp_all

      split
      · next steck_ne_nil_after =>
        simp
        simp at prior_invar
        intro x x_in_stack_after
        unfold bfs_step_expand at ⊢ x_in_stack_after
        simp_all
        split
        · next x_visited_before =>
          have tail_ne_nil : tail ≠ [] := by
              intro tail_empty
              simp_all
          simp [tail_ne_nil]
          simp_all

          have tail_compose_head_tail : ∃ new_head : V, ∃ tail_tail : List V, tail = new_head :: tail_tail := by
            apply List.ne_nil_iff_exists_cons.mp at tail_ne_nil
            exact tail_ne_nil

          obtain ⟨ new_head, tail_tail, tail_compose ⟩ := tail_compose_head_tail

          have tail_head_is : ∀ (p : tail ≠ []), tail.head p = new_head := by
            intro p
            apply List.head_of_head?_eq_some -- direct rw produces motive error (due to proof)
            rw [tail_compose]
            simp

          rw [tail_head_is]
          clear tail_head_is
          have h1 := prior_invar new_head
          have h2 := prior_invar x
          simp_all
          have h3 : state.pathOrder new_head ≥ state.pathOrder head := by
            unfold bfs_stack_sorted at stack_sorted
            rw [compose] at stack_sorted
            simp at stack_sorted
            exact stack_sorted.left.left
          omega
        · next x_not_visited_before =>
          -- i.e. x is newly visited
          cases x_in_stack_after
          · next x_in_tail =>
            simp_all -- contradictory
          · next both =>
            obtain ⟨ head_adj_x, _ignore ⟩ := both
            clear _ignore
            by_cases tail_eq_nil : tail = []
            · simp_all
              split
              · next h =>
                simp_all
                exfalso
                apply option_mem at h
                obtain ⟨ y, find_some_is_y, y_in_visited ⟩ := h
                apply Option.eq_some_if_get_eq at find_some_is_y
                apply List.findSome?_eq_some_iff.mp at find_some_is_y
                obtain ⟨l_1, a, l_2, ⟨l_compoise,a_test,rest⟩ ⟩ := find_some_is_y
                simp at a_test
                simp_all
                have a_ne_mem_visited : a ∉ state.visited := a_test.left.right
                have a_eq_y : a = y := a_test.right
                rw [a_eq_y] at a_ne_mem_visited
                contradiction
              · simp
            · simp_all
              unfold bfs_stack_sorted at stack_sorted
              rw [compose] at stack_sorted
              simp at stack_sorted
              rw [add_comm]
              apply Nat.add_le_add
              · apply stack_sorted.left
                simp
              · rfl
      · rfl

lemma bfs_expand_keeps_on_stack_or_nei_max_order(goal : V)
    (state : base_search_state g ℕ)
    (on_stack_or_nei_visited : search_invar_on_stack_or_all_neighbours_visited state)
    (max_diff_invar : bfs_stack_max_diff state)
    (stack_shortest : bfs_stack_shortest_path start state)
    (extract_length_invar : bfs_path_as_extracted_as_long_as_sort_index start state)
    (mother_invar : search_invar_mother_is_visited state)
    (mother_invar_adj : search_invar_mother_is_adjacent start state)
    (decreasing_invar : search_invar_mother_decreasing_path_order start state)
    :
     ∀ head : V, ∀ tail : List V,
        bfs_invar_on_stack_or_all_neighbours_max_order  state
          ∧ head ≠ goal
          ∧ state.stack = head :: tail
        → bfs_invar_on_stack_or_all_neighbours_max_order  (bfs_step_expand g state head tail) := by
      unfold bfs_invar_on_stack_or_all_neighbours_max_order
      simp
      intro head tail prior_invar head_ne_goal compose a a_visited_after a_not_on_stack_after y a_adj_y

      unfold bfs_step_expand at a_visited_after a_not_on_stack_after
      simp at a_visited_after a_not_on_stack_after
      obtain ⟨ a_not_in_tail, a_visi_if_head_adj ⟩ := a_not_on_stack_after
      cases a_visited_after
      · next a_visited_before =>
        by_cases a_eq_head : a = head
        · rw [a_eq_head] at ⊢ a_adj_y a_not_in_tail a_visi_if_head_adj a_visited_before
          clear a_eq_head a a_visi_if_head_adj
          by_cases y_visited_before : y ∈ state.visited
          · unfold bfs_step_expand
            simp [y_visited_before, a_visited_before]
            by_cases y_on_stack : y ∈ state.stack
            · unfold bfs_stack_max_diff at max_diff_invar
              grind
            · unfold bfs_stack_shortest_path at stack_shortest
              have shortest_dist_y := stack_shortest y y_visited_before (Or.inl y_on_stack)
              unfold distance_is at shortest_dist_y
              obtain ⟨ p,p_length_order, length_is_shortest⟩ := shortest_dist_y
              by_contra p_longer_than_head_y
              simp at p_longer_than_head_y
              rw [← p_length_order] at p_longer_than_head_y
              unfold Path.is_shortest at length_is_shortest
              have path_to_y_legth_head_plus_one : ∃ p' : g.Walk start y, p'.length = 1 + state.pathOrder head := by
                let p := (extract_path_to start head state a_visited_before mother_invar mother_invar_adj decreasing_invar).fst
                let p' := p.val.concat a_adj_y
                use p'
                unfold p'
                rw [Walk.concat_inc_length_by_one]
                unfold bfs_path_as_extracted_as_long_as_sort_index at extract_length_invar
                rw [← extract_length_invar]
                unfold Path.length p
                congr
                · use mother_invar
                · use mother_invar_adj
                · use decreasing_invar
                · use a_visited_before
              obtain ⟨w',w'_length⟩ := path_to_y_legth_head_plus_one
              rw [← w'_length] at p_longer_than_head_y
              obtain ⟨ p', p'_leq_w'⟩ := w'.shorter_path_exists
              have p'_longer := length_is_shortest p'
              omega
          · unfold bfs_step_expand
            simp [y_visited_before, a_visited_before]
            grind
        · unfold bfs_step_expand
          simp_all
          split
          · next y_visited_before =>
            simp_all
          · split
            · simp
            · next y_not_visited_before visi_ne_empty =>
              grind -- contradicts not on stack -> nei visited
      · next both =>
        obtain ⟨ head_adj_a, a_ne_visited ⟩ := both
        grind -- contradictory

lemma bfs_expand_keeps_stack_sorted(goal : V)
    (state : base_search_state g ℕ)
    (stack_visited_invar : search_invar_stack_is_visited state)
    (max_diff_invar : bfs_stack_max_diff state)
    :
     ∀ head : V, ∀ tail : List V,
        bfs_stack_sorted  state
          ∧ head ≠ goal
          ∧ state.stack = head :: tail
        → bfs_stack_sorted  (bfs_step_expand g state head tail) := by
    intro head tail ⟨ prior_sorted, head_ne_goal, stack_compose ⟩
    unfold bfs_stack_sorted
    unfold bfs_step_expand
    simp_all
    apply List.pairwise_append.mpr
    and_intros
    · apply List.Pairwise.imp_of_mem
      case refine_1.p =>
        unfold bfs_stack_sorted at prior_sorted
        rw [stack_compose] at prior_sorted
        simp at prior_sorted
        refine prior_sorted.right
      intro a b a_in_tail b_in_tail a_order_leq_b_order
      grind
    · apply List.Pairwise.filterMap
      case refine_2.refine_1.R => use fun _ _ => true
      · intro a a' _ b b_some b' b'_some
        simp_all
        have b_ne_visi : b ∉ state.visited := by rw [b_some.right] at b_some ; exact b_some.left.right
        have b'_ne_visi : b' ∉ state.visited := by rw [b'_some.right] at b'_some ; exact b'_some.left.right
        simp_all
      · apply List.pairwise_of_forall
        simp
    · intro a a_in_tail b b_in_new_visited
      have a_visited : a ∈ state.visited := by grind
      have visi_ne_empty : state.visited ≠ ∅ := by grind
      have b_not_visited : b ∉ state.visited := by grind
      grind

set_option maxHeartbeats 10000000 in
lemma bfs_expand_keeps_shortest_path_invar
    (start : V) (goal : V)
    (state : base_search_state g ℕ)
    ----- co-invariants needed for path extraction
    (mother_invar : search_invar_mother_is_visited state)
    (mother_invar_adj : search_invar_mother_is_adjacent start state)
    (decreasing_invar : search_invar_mother_decreasing_path_order start state)
    (start_visited : search_invar_start_visited start state)
    (on_stack_or_nei_visited : search_invar_on_stack_or_all_neighbours_visited state)
    (stack_visited_invar : search_invar_stack_is_visited state)
    -- new bfs_ specific invars
    (extract_length_invar : bfs_path_as_extracted_as_long_as_sort_index start state)
    (update_invar : bfs_invar_on_stack_or_all_neighbours_max_order state)
    (stack_sorted : bfs_stack_sorted state)
    (max_diff_invar : bfs_stack_max_diff state)
    (start_path_order : search_invar_start_path_order_zero start state)
    :
     ∀ head : V, ∀ tail : List V,
        bfs_stack_shortest_path start state
          ∧ ¬ head = goal
          ∧ state.stack = head :: tail
        → bfs_stack_shortest_path start (bfs_step_expand g state head tail) := by
    intro head tail ⟨prior_invar,head_is_not_goal,compose⟩
    unfold bfs_stack_shortest_path --at prior_invar ⊢
    intro v v_visited not_on_stack_or_head

    simp at compose v_visited not_on_stack_or_head prior_invar ⊢

    by_cases v_not_start : v ≠ start
    · cases not_on_stack_or_head
      · next v_not_on_stack =>
        have h := prior_invar v
        clear prior_invar
        unfold bfs_step_expand at v_not_on_stack v_visited ⊢
        simp at v_visited
        cases v_visited
        · next v_was_visited =>
          simp_all
          apply h
          by_cases hh : head = v
          · right; exact hh
          · left ; intro hhh ; symm at hhh ; contradiction
        · next both =>
          obtain ⟨ head_adj_v, v_was_not_visited ⟩ := both
          simp_all -- contractiction. This case is impossible
      · next v_now_stack_head =>
        simp at v_now_stack_head
        obtain ⟨ stack_not_empty_after, head_after_is_v ⟩ := v_now_stack_head
        unfold bfs_step_expand at stack_not_empty_after head_after_is_v v_visited ⊢
        simp at v_visited

        cases v_visited
        · next v_was_visited_before=>
          -- v is *now* the head of the stack, but it was already visited before.
          -- this means it had to already have been on the stack before


          have t_c : ∃ tail_tail : List V, tail = v :: tail_tail := by
            by_cases tail_ne_empty : tail ≠ []
            · apply List.ne_nil_iff_exists_cons.mp at tail_ne_empty
              obtain ⟨ b, tail_tail, cons ⟩ := tail_ne_empty
              use tail_tail
              rw [cons]
              simp_all
            · simp_all
              apply Option.eq_some_if_get_eq at head_after_is_v
              apply List.findSome?_eq_some_iff.mp at head_after_is_v
              obtain ⟨l_1, a, l_2, ⟨ p,q,r⟩ ⟩ := head_after_is_v
              simp_all
              obtain ⟨ ⟨ x1,x_2⟩ ,y⟩ := q
              rw [y] at x_2
              contradiction
          unfold distance_is

          -- this will be the same path as after the bfs_expand
          -- for Dijkstra, this might be a different path, as it could be that head and v are adjacent and the path gets updated. But for BFS, this update is simply ignored as we "know" that that path can only be at most as long as the one that we have
          let path_to_v : g.Path start v :=
            (extract_path_to start v state v_was_visited_before mother_invar mother_invar_adj decreasing_invar).1

          use path_to_v
          constructor
          · simp_all
            apply extract_length_invar mother_invar mother_invar_adj decreasing_invar v
          · unfold Path.is_shortest
            intro p'
            by_contra p'_is_shorter

            have p'_elem_on_stack_or_v_visited :
              (∃ u ∈ p'.support, u ∈ state.stack ∧ u ≠ v ∧ (p'.support.takeWhile (· ≠ u)).all (· ∉ state.stack)) ∨
                (v ∈ state.visited ∧ ∀ u ∈ p'.support, u ≠ v → u ∉ state.stack ∧ u ∈ state.visited) := run_path_through_state_yields_node_on_stack_or_all_visited start v v_not_start p' state start_visited on_stack_or_nei_visited

            cases p'_elem_on_stack_or_v_visited
            · next u_in_support_on_stack =>
              obtain ⟨u, ⟨u_in_support, ⟨ u_on_stack, u_ne_v, all_prior_not_on_stack ⟩ ⟩ ⟩ := u_in_support_on_stack
              have path_length_is_pathOrder : path_to_v.length = state.pathOrder v := by
                apply extract_length_invar mother_invar mother_invar_adj decreasing_invar
              have order_u_le_path_length_p' : state.pathOrder u < p'.length := by
                apply order_u_le_path_length_p
                · exact update_invar
                · exact on_stack_or_nei_visited
                · exact start_path_order
                · exact start_visited
                · exact u_in_support
                · exact u_on_stack
                · exact all_prior_not_on_stack
                · exact u_ne_v

              by_cases u_ne_head : u ≠ head
              · have v_before_u_on_stack : state.pathOrder v ≤ state.pathOrder u := by
                  unfold bfs_stack_sorted at stack_sorted
                  rw [compose] at stack_sorted
                  simp at stack_sorted
                  obtain ⟨ _ignore, tail_sorted⟩ := stack_sorted
                  obtain ⟨ tail_tail, tail_compose ⟩ := t_c
                  rw [tail_compose] at tail_sorted
                  simp at tail_sorted
                  apply tail_sorted.left u
                  rw [compose] at u_on_stack
                  rw [tail_compose] at u_on_stack
                  simp at u_on_stack
                  simp_all
                omega
              · simp_all

                -- stack criterion for BFS, they differ by at most one
                -- in Dijkstra this will be replaced by the update performed by the expansion (then with cost instead of 1), but only if adjacent
                have v_at_most_one_larger_than_head : state.pathOrder v ≤ state.pathOrder head + 1 := by
                  apply GE.ge.le
                  apply max_diff_invar
                  obtain ⟨ tail_tail, tail_compose⟩ := t_c
                  rw [tail_compose]
                  simp

                omega
            · next both =>
              obtain ⟨v_visited, support_not_on_stack⟩ := both
              obtain ⟨ w,path_start_w,w_adj_v,v_not_earlier_in_path,p'_compose⟩ := p'.split_at_end (Ne.symm v_not_start)
              have path_start_w_length : path_start_w.length + 1 = p'.length := by
                unfold Path.length
                rw [p'_compose]
                apply Eq.symm
                rw [add_comm]
                apply Path.concat_inc_length_by_one
                exact v_not_earlier_in_path
              rw [← path_start_w_length] at p'_is_shorter
              clear path_start_w_length
              have w_in_supp : w ∈ p'.val.support := by rw [p'_compose] ; simp
              have w_ne_v : w ≠ v := by
                by_contra w_eq_v
                rw [← w_eq_v] at v_not_earlier_in_path
                have w_in_supp : w ∈ path_start_w.val.support := Path.goal_in_support path_start_w
                contradiction
              have w_visited : w ∈ state.visited := (support_not_on_stack w w_in_supp w_ne_v).right
              have w_not_on_stack : w ∉ state.stack := (support_not_on_stack w w_in_supp w_ne_v).left

              have w_not_head : w ≠ head := by rw [compose] at w_not_on_stack ; simp_all
              have w_not_in_tail : w ∉ tail := by rw [compose] at w_not_on_stack ; simp_all

              unfold bfs_invar_on_stack_or_all_neighbours_max_order at update_invar
              rw [compose] at update_invar
              simp at update_invar
              have w_nei_updated := update_invar w w_visited w_not_head w_not_in_tail v w_adj_v
              have w_dist_is_order := prior_invar w w_visited (Or.inl w_not_on_stack)
              unfold distance_is at w_dist_is_order
              obtain ⟨shortest_to_w, ⟨w_len,is_shortest⟩ ⟩ := w_dist_is_order
              unfold Path.is_shortest at is_shortest
              simp at w_nei_updated
              rw [←w_len] at w_nei_updated
              have path_to_v_has_order_length := extract_length_invar mother_invar mother_invar_adj decreasing_invar v v_was_visited_before
              unfold path_to_v at p'_is_shorter
              rw [path_to_v_has_order_length] at p'_is_shorter
              clear path_to_v_has_order_length
              simp at p'_is_shorter
              have path_start_w_shorter_than_shortest := lt_of_lt_of_le p'_is_shorter w_nei_updated
              have path_start_w_longer_than_shortest := is_shortest path_start_w
              simp_all
              omega
        · next both =>
          obtain ⟨ head_adj_v, v_not_visited_before ⟩ := both
          split
          · next visited_empty =>
            clear stack_not_empty_after head_after_is_v
            have head_in_stack : head ∈ state.stack := by simp_all
            apply stack_visited_invar at head_in_stack
            simp_all -- by contradiction
          · next visited_not_empty =>
            by_cases tail_empty : tail = []
            · --simp_all
              clear stack_not_empty_after head_after_is_v
              unfold distance_is
              -- we newly inserted v as the neighbour of head and it became the stack head immediately

              have head_was_visited_before : head ∈ state.visited := by simp_all
              let path_to_head : g.Path start head :=
                (extract_path_to start head state head_was_visited_before mother_invar mother_invar_adj decreasing_invar).1
              have support_visited : ∀ u ∈ path_to_head.val.support, u ∈ state.visited := by
                apply support_of_path_visited
                unfold path_to_head
                rfl

              let path_to_v : g.Path start v := path_to_head.concat head_adj_v (by
                by_contra v_in_support
                have v_visited_before := support_visited v v_in_support
                contradiction)
              use path_to_v
              constructor
              · simp_all
                unfold bfs_path_as_extracted_as_long_as_sort_index at extract_length_invar
                have hh := extract_length_invar mother_invar mother_invar_adj decreasing_invar head head_was_visited_before
                rw [← hh]
                unfold path_to_v
                unfold path_to_head
                apply Path.concat_inc_length_by_one
              · unfold Path.is_shortest
                intro p'
                by_contra p'_is_shorter
                simp at p'_is_shorter

                have p'_elem_on_stack_or_v_visited :
                  (∃ u ∈ p'.val.support, u ∈ state.stack ∧ u ≠ v ∧ (p'.support.takeWhile (· ≠ u)).all (· ∉ state.stack)) ∨
                    (v ∈ state.visited ∧ ∀ u ∈ p'.val.support, u ≠ v → u ∉ state.stack ∧ u ∈ state.visited) :=
                  run_path_through_state_yields_node_on_stack_or_all_visited start v v_not_start p' state start_visited on_stack_or_nei_visited


                cases p'_elem_on_stack_or_v_visited
                · next u_in_support_on_stack =>
                  obtain ⟨u, ⟨u_in_support, ⟨ u_on_stack, u_ne_v, _⟩ ⟩ ⟩ := u_in_support_on_stack
                  rw [compose] at u_on_stack
                  simp at u_on_stack
                  simp_all
                  obtain ⟨ path_to_head_on_p', shorter⟩ := p'.contains_subpath u_in_support u_ne_v
                  unfold path_to_v at p'_is_shorter
                  unfold Path.concat at p'_is_shorter
                  --simp at p'_is_shorter
                  rw [← Path.length_same] at p'_is_shorter
                  unfold bfs_stack_shortest_path at prior_invar
                  simp_all
                  have head_shortest := prior_invar head head_was_visited_before
                  simp at head_shortest
                  unfold distance_is at head_shortest
                  obtain ⟨ actual_shortest_to_head, x, xx ⟩ := head_shortest
                  unfold Path.is_shortest at xx
                  have xxx := xx path_to_head_on_p'
                  rw [x] at xxx
                  have xxxx := extract_length_invar mother_invar mother_invar_adj decreasing_invar head head_was_visited_before
                  unfold path_to_head at p'_is_shorter
                  simp_all
                  omega
                · next h =>
                  have v_visited := h.left
                  contradiction

            · have v_was_on_stack : v ∈ state.stack := by
                rw [compose]
                apply List.mem_cons.mpr
                right
                simp_all
                apply List.mem_of_head?
                rw [← head_after_is_v]
                apply List.head?_eq_some_head
              have v_visited_before : v ∈ state.visited := stack_visited_invar v v_was_on_stack
              contradiction
    · simp at v_not_start
      rw [v_not_start]
      unfold distance_is
      unfold search_invar_start_path_order_zero at start_path_order
      have gg := start_path_order
      have still_zero : (bfs_step_expand g state head tail).pathOrder start = 0 := by
        apply bfs_expand_start_path_order_zero_carries
        · apply start_visited
        · constructor
          · apply start_path_order
          · constructor
            · apply head_is_not_goal
            · apply compose

      rw [still_zero]
      use (g.nil_path start)
      unfold Path.is_shortest
      constructor <;> rw [Path.length_nil_zero] ; simp


lemma bfs_expand_carries_all_bfs_invars (start : V) (goal : V):
      base_invar_carries_over_expand (bfs_step_expand g) goal (bfs_all_invar (g:=g) start) := by
      unfold base_invar_carries_over_expand
      intro s head tail ⟨ invar_before, head_ne_goal, compose⟩
      unfold bfs_all_invar
      constructor
      · apply bfs_expand_keeps_base_invars
        · exact ⟨ invar_before.left, head_ne_goal, compose⟩
      · and_intros
        · apply bfs_expand_keeps_shortest_path_invar
          · exact invar_before.left.right.left
          · exact invar_before.left.right.right.left
          · exact invar_before.left.right.right.right.left
          · exact invar_before.left.right.right.right.right.right
          · exact invar_before.left.right.right.right.right.left
          · exact invar_before.left.left
          · exact invar_before.right.right.left
          · exact invar_before.right.right.right.left
          · exact invar_before.right.right.right.right.left
          · exact invar_before.right.right.right.right.right.left
          · exact invar_before.right.right.right.right.right.right
          · exact ⟨ invar_before.right.left, head_ne_goal, compose⟩
        · apply bfs_expand_keeps_extracted_same_length_as_sort_index
          · exact invar_before.left.right.right.right.right.right
          · exact invar_before.left.right.left
          · exact invar_before.left.right.right.left
          · exact invar_before.left.right.right.right.left
          · exact invar_before.left.left
          · exact ⟨ invar_before.right.right.left, head_ne_goal, compose⟩
        · apply bfs_expand_keeps_on_stack_or_nei_max_order
          · exact invar_before.left.right.right.right.right.left
          · exact invar_before.right.right.right.right.right.left
          · exact invar_before.right.left
          · exact invar_before.right.right.left
          · exact invar_before.left.right.left
          · exact invar_before.left.right.right.left
          · exact invar_before.left.right.right.right.left
          · exact ⟨ invar_before.right.right.right.left, head_ne_goal, compose⟩
        · apply bfs_expand_keeps_stack_sorted
          · exact invar_before.left.left
          · exact invar_before.right.right.right.right.right.left
          · exact ⟨ invar_before.right.right.right.right.left, head_ne_goal, compose⟩
        · apply bfs_expand_keeps_max_diff
          · exact invar_before.left.left
          · exact invar_before.right.right.right.right.left
          · exact ⟨ invar_before.right.right.right.right.right.left, head_ne_goal, compose⟩
        · apply bfs_expand_start_path_order_zero_carries
          · exact invar_before.left.right.right.right.right.right
          · exact ⟨ invar_before.right.right.right.right.right.right, head_ne_goal, compose⟩

lemma bfs_invar_holds_at_init (start : V):
      bfs_all_invar start (base_search_state_initial (G:=g) start 0) := by
      constructor
      · apply base_search_state_initial_all_basic_invars
      · and_intros
        · unfold bfs_stack_shortest_path
          unfold base_search_state_initial
          unfold distance_is
          simp
          use g.nil_path start
          unfold Path.is_shortest
          simp
        · unfold bfs_path_as_extracted_as_long_as_sort_index
          unfold base_search_state_initial
          simp
          intro u u_is_start
          unfold Walk.length
          unfold extract_path_to
          simp
          split
          · next h=>
            simp_all
            subst u_is_start
            simp_all only [reduceCtorEq]
          · simp
        · unfold bfs_invar_on_stack_or_all_neighbours_max_order
          unfold base_search_state_initial
          simp
        · unfold bfs_stack_sorted
          unfold base_search_state_initial
          simp
        · unfold bfs_stack_max_diff
          unfold base_search_state_initial
          simp
        · unfold search_invar_start_path_order_zero
          unfold base_search_state_initial
          simp

theorem bfs_is_optimal(g: WeightedDiGraph V E) (start : V) (goal : V)
    (returned_path : Option.isSome (bfs g start goal)):
    ((bfs g start goal).get returned_path).is_shortest := by

    let final := search_with_stack_step (goal:=goal) (start_state := base_search_state_initial start 0) (bfs_step_expand g) bfs_expand_metric_reduction
    let final_state := final.1

    -- general properties
    have h_4 : search_prop_stack_head_is_goal goal final_state := by
      --intro terminated_with_goal_found
      --unfold search_prop_stack_head_is_goal
      unfold final_state
      unfold final
      unfold search_with_stack_step
      simp
      unfold search_internal
      apply search_recurse_obtain_base_termination_property goal (base_search_state_initial start 0) (property_after_termination := search_prop_stack_head_is_goal goal ) (terminated_with := true) (search_step := search_stack_step (bfs_step_expand g))
      · intro s
        apply search_stack_step_goal_stack_head_if_terminated
      · unfold bfs at returned_path
        unfold search_exe_with_stack_step at returned_path
        unfold search_exe at returned_path
        simp_all
        apply returned_path

    have t_0 : search_invar_stack_is_visited final_state := by
      unfold final_state
      unfold final
      unfold search_with_stack_step
      simp only []
      apply search_returns_with_stack_visited (state_type := base_search_state g ℕ) (start_state := base_search_state_initial start 0) (start := start)
      · rfl
      · apply base_invar_carries_over_stack_step
        apply bfs_expand_keeps_base_invars

    have h_3 : search_prop_goal_visited goal final_state := by
      apply t_0
      unfold search_prop_stack_head_is_goal at h_4
      apply List.eq_cons_of_mem_head? at h_4
      rw [h_4]
      simp

    have t_1 : search_invar_mother_is_visited final_state := by
      unfold final_state
      unfold final
      unfold search_with_stack_step
      simp only []
      apply search_returns_with_mother_visited (state_type := base_search_state g ℕ) (start_state := base_search_state_initial start 0) (start := start)
      · rfl
      · apply base_invar_carries_over_stack_step
        apply bfs_expand_keeps_base_invars

    have t_2 : search_invar_mother_is_adjacent start final_state := by
      unfold final_state
      unfold final
      unfold search_with_stack_step
      simp only []
      apply search_returns_with_mother_adjacent (state_type := base_search_state g ℕ) (start_state := base_search_state_initial start 0) (start := start)
      · rfl
      · apply base_invar_carries_over_stack_step
        apply bfs_expand_keeps_base_invars

    have t_3 : search_invar_mother_decreasing_path_order start final_state := by
      unfold final_state
      unfold final
      unfold search_with_stack_step
      simp only []
      apply search_returns_with_mother_decreasing (state_type := base_search_state g ℕ) (start_state := base_search_state_initial start 0) (start := start)
      · rfl
      · apply base_invar_carries_over_stack_step
        apply bfs_expand_keeps_base_invars


    -- BFS specific ones
    have bfs_full_invar_at_end : bfs_all_invar start final_state := by
     have right_class : (fun s => bfs_all_invar start (has_base_search_state.to_base_state (G:=g) s)) final_state := by
      unfold final_state
      unfold final
      unfold search_with_stack_step
      unfold search_internal
      simp
      apply search_recurse_lift_base_invariant
      constructor
      · apply bfs_invar_holds_at_init
      · apply base_invar_carries_over_stack_step
        apply bfs_expand_carries_all_bfs_invars
     -- needs to be applied, lean4 has problems with they type-class here
     apply right_class

    have i_1 : bfs_stack_shortest_path start final_state := bfs_full_invar_at_end.2.1

    have h_2 : bfs_path_as_extracted_as_long_as_sort_index start final_state := bfs_full_invar_at_end.2.2.1


    have h : g.distance_is start goal (final_state.pathOrder goal) := by
      unfold distance_is
      unfold bfs_stack_shortest_path at i_1
      have i_1' := i_1 goal h_3
      have i_1'' : g.distance_is start goal (final_state.pathOrder goal) := by
        unfold search_prop_stack_head_is_goal at h_4
        apply i_1'
        right
        simp_all
        obtain ⟨ tail, compose ⟩ := List.head?_eq_some_iff.mp h_4
        simp_all
      unfold distance_is at i_1''
      exact i_1''


    unfold bfs
    unfold search_exe_with_stack_step
    unfold search_exe
    unfold Path.is_shortest
    intro p'
    unfold distance_is at h
    obtain ⟨p, ⟨ p_path_length, p_is_shortest ⟩ ⟩  := h

    unfold bfs_path_as_extracted_as_long_as_sort_index at h_2
    have prop := h_2 t_1 t_2 t_3 goal
    clear h_2
    unfold final_state at prop
    unfold final at prop
    unfold search_with_stack_step at prop
    simp_all
    unfold has_base_search_state.to_base_state
    unfold instHas_base_search_stateBase_search_state
    rw [prop]
    clear prop t_1 t_2 t_3
    unfold final_state at p_path_length
    unfold final at p_path_length
    unfold search_with_stack_step at p_path_length
    simp_all
    rw [← p_path_length]
    unfold Path.is_shortest at p_is_shortest
    specialize p_is_shortest p'
    simp_all


end WeightedDiGraph
