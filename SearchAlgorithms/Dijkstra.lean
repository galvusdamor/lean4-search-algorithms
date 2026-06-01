-- Dijkstra is a special case of A' -- when h = 0
import Graphlib.HeuristicSearch

-- def local global variable for a graph
variable {V : Type} [FinEnum V] [DecidableEq V]
variable {g : NatGraph V}


namespace NatGraph

open WeightedDiGraph

/-! ## Dijkstra implementation and proof -/

@[simp]
def h_zero (_ : V) : ℕ := 0

def dijkstra (start : V) (goal : V): Option (g.Path start goal) :=
  let start_state := WeightedDiGraph.base_search_state_initial start ⟨0,0⟩
  have h : WeightedDiGraph.has_base_search_state.to_base_state (G:=g) start_state = WeightedDiGraph.base_search_state_initial start (0,0):= by simp_all only [start_state]; rfl

  WeightedDiGraph.search_exe_with_stack_step (G:=g) (start := start) (goal:=goal) (start_state:=start_state) (termination_metric := hsearch_termination_metric) (hsearch_step_expand h_zero) (hsearch_expand_metric_reduction h_zero) (hsearch_expand_keeps_base_invars h_zero) h

def dijkstra_last_state (start : V) (goal : V): WeightedDiGraph.base_search_state g (ℕ×ℕ) × Bool :=
  WeightedDiGraph.search_with_stack_step (goal:=goal) (start_state := WeightedDiGraph.base_search_state_initial start (0,0)) (hsearch_step_expand h_zero) (hsearch_expand_metric_reduction h_zero)

theorem dijkstra_is_sound (start : V) (goal : V) :
    (Option.isSome (dijkstra (g:=g) start goal) → (∃ x : (g.Path start goal), x = x)) := by
  apply WeightedDiGraph.search_with_stack_step_is_sound
  · apply hsearch_expand_metric_reduction
  · apply hsearch_expand_keeps_base_invars
  · rfl

theorem dijkstra_is_complete (start : V) (goal : V):
    ((∃ x : (g.Path start goal), x = x) → Option.isSome (dijkstra (g:=g) start goal)) := by
  apply WeightedDiGraph.search_with_stack_step_is_complete
  · apply hsearch_expand_metric_reduction
  · apply hsearch_expand_keeps_base_invars
  · rfl
  · apply hsearch_expand_keeps_goal_on_stack
  · apply hsearch_expand_goal_becomes_visited_puts_it_on_stack

/-! ## Invariants for Dijkstra -/

/- The differene in path order between a node an its mother corresponds to the difference in path
length between them. The mother however might have an even *lower* path order if it has been
updated, but that update has not been propagated to the child yet. -/
abbrev dijkstra_path_order_diff_by_one (start : V) (s : WeightedDiGraph.base_search_state g (ℕ×ℕ)) :=
    ∀ u : V, (h : u ∈ s.visited) → (ne_start : u ≠ start) →
      (s.pathOrder u).2 ≥ (s.pathOrder (s.mother ⟨u,h⟩)).2 + 1

/-- The stack is sorted by the path_order (i.e. distance) value. -/
abbrev dijkstra_stack_sorted (s : WeightedDiGraph.base_search_state g (ℕ×ℕ)) :=
  List.Pairwise (fun u v => (s.pathOrder u = s.pathOrder v) ∨ (s.pathOrder u ≺ s.pathOrder v)) s.stack

abbrev dijkstra_stack_shortest_path (start : V) (s : WeightedDiGraph.base_search_state g (ℕ×ℕ)) :=
  ∀ u ∈ s.visited, u ∉ s.stack ∨ (if ne : s.stack ≠ [] then s.stack.head ne = u else false) →
    g.cost_is start u (s.pathOrder u).1

@[simp]
abbrev search_invar_start_not_mem_tail (start : V) (s : WeightedDiGraph.base_search_state g (ℕ×ℕ)) :=
      start ∉ s.stack.tail

@[simp]
abbrev search_invar_stack_nodup (s : WeightedDiGraph.base_search_state g (ℕ×ℕ)) :=
      ∀ v : V, s.stack.count v ≤ 1

abbrev dijkstra_all_invar (start : V) (s : WeightedDiGraph.base_search_state g (ℕ×ℕ)) :=
      WeightedDiGraph.search_invar_all_basic start s
    ∧ dijkstra_stack_shortest_path start s
    ∧ hsearch_path_order_diff_by_edge_cost start s
    ∧ hsearch_invar_on_stack_or_all_neighbours_max_order s
    ∧ dijkstra_stack_sorted s
    ∧ hsearch_invar_start_path_order_zero_zero start s
    ∧ search_invar_start_not_mem_tail start s
    ∧ search_invar_stack_nodup s

lemma dijkstra_invar_holds_at_init (start : V):
      dijkstra_all_invar start (WeightedDiGraph.base_search_state_initial (G:=g) start (0,0)) := by
  constructor
  · apply WeightedDiGraph.base_search_state_initial_all_basic_invars
  · and_intros
    · unfold dijkstra_stack_shortest_path
      unfold WeightedDiGraph.base_search_state_initial
      unfold cost_is
      simp
      use g.nil_path start
      unfold WeightedDiGraph.Path.is_cheapest
      and_intros
      · apply WeightedDiGraph.Path.cost_nil_zero
      · simp
        intro a nodup
        rw [← WeightedDiGraph.Path.cost]
        rw [WeightedDiGraph.Path.cost_nil_zero]
        simp_all
    · unfold hsearch_path_order_diff_by_edge_cost
      unfold WeightedDiGraph.base_search_state_initial
      simp
      intro u u_is_start u_ne_start
      grind
    · unfold hsearch_invar_on_stack_or_all_neighbours_max_order
      unfold WeightedDiGraph.base_search_state_initial
      simp
    · unfold dijkstra_stack_sorted
      unfold WeightedDiGraph.base_search_state_initial
      simp
    · unfold hsearch_invar_start_path_order_zero_zero
      unfold WeightedDiGraph.base_search_state_initial
      simp
    · unfold search_invar_start_not_mem_tail
      unfold WeightedDiGraph.base_search_state_initial
      simp
    · unfold search_invar_stack_nodup
      unfold WeightedDiGraph.base_search_state_initial
      simp
      grind

section
variable (state : WeightedDiGraph.base_search_state g (ℕ×ℕ))

lemma dijkstra_expand_start_not_mem_tail_carries (start : V) (goal : V)
    (start_visited : WeightedDiGraph.search_invar_start_visited start state)
    (start_zero_zero : hsearch_invar_start_path_order_zero_zero start state)
    :
     ∀ head : V, ∀ tail : List V,
        search_invar_start_not_mem_tail start state
          ∧ ¬ head = goal
          ∧ state.stack = head :: tail
        → search_invar_start_not_mem_tail start (hsearch_step_expand h_zero state head tail) := by
      intro head tail ⟨ prior_invar,head_ne_goal,compose⟩
      unfold search_invar_start_not_mem_tail
      unfold hsearch_invar_start_path_order_zero_zero at start_zero_zero
      unfold hsearch_step_expand
      simp_all
      intro start_in
      apply List.mem_of_mem_tail at start_in
      simp at start_in
      grind

lemma dijkstra_expand_stack_nodup_carries (goal : V)
    (stack_visited : WeightedDiGraph.search_invar_stack_is_visited state)
    : ∀ head : V, ∀ tail : List V,
        search_invar_stack_nodup state
          ∧ ¬ head = goal
          ∧ state.stack = head :: tail
        → search_invar_stack_nodup (hsearch_step_expand h_zero state head tail) := by
  intro head tail ⟨ prior_invar,head_ne_goal,compose⟩
  unfold search_invar_stack_nodup
  intro v
  unfold hsearch_step_expand
  simp_all
  rw [mergeSort_count]
  by_cases v_not_mem_tail : v ∉ tail --v_eq_head : v = head
  · have tail_count : List.count v tail = 0 := by
      apply List.count_eq_zero.mpr
      assumption
    simp [tail_count]
    apply List.nodup_iff_count_le_one.mp
    apply List.Nodup.filterMap
    · grind
    · unfold List.unattach
      apply List.Nodup.map
      · simp
      · simp
  · simp at v_not_mem_tail ; rename v ∈ tail => v_mem_tail
    simp
    have count_tail_eq_one : List.count v tail = 1 := by
      apply eq_of_le_of_ge
      · specialize prior_invar v
        rw [List.count_cons] at prior_invar
        simp at prior_invar
        apply le_trans ; rotate_left
        · apply prior_invar
        · simp
      · simp
        assumption
    simp_all
    apply List.count_eq_zero.mpr
    simp
    intro adj_head_v
    constructor
    · apply stack_visited.right
      assumption
    · intro v_visited v_not_in_tail
      contradiction

lemma dijkstra_expand_keeps_shortest_path_invar_start
    (start : V) (goal : V)
    (start_visited : WeightedDiGraph.search_invar_start_visited start state)
    (start_path_order : hsearch_invar_start_path_order_zero_zero start state)
    (head : V) (tail : List V)
    (head_is_not_goal : ¬head = goal)
    (compose : state.stack = head :: tail):
     g.cost_is start start ((hsearch_step_expand h_zero state head tail).pathOrder start).1
     := by
  unfold cost_is
  unfold hsearch_invar_start_path_order_zero_zero at start_path_order
  have gg := start_path_order
  have still_zero : (hsearch_step_expand h_zero state head tail).pathOrder start = 0 := by
    apply hsearch_expand_start_path_order_zero_carries
    · apply start_visited
    · constructor
      · apply start_path_order
      · constructor
        · apply head_is_not_goal
        · apply compose
  rw [still_zero]
  use (g.nil_path start)
  unfold Path.is_cheapest
  constructor
  all_goals
    rw [Path.cost_nil_zero]
    simp

lemma dijkstra_new_head_cost_lt_other_on_stack_before
    (head : V) (tail : List V) (compose : state.stack = head :: tail)
    (u : V) (u_on_stack : u ∈ state.stack) (u_ne_head : u ≠ head)
    (u_visited : u ∈ state.visited)
    (v : V) (after_not_nil : (hsearch_step_expand h_zero state head tail).stack ≠ [])
    (adj_head_v : g.Adj head v)
    (v_head_after : (hsearch_step_expand h_zero state head tail).stack.head after_not_nil = v):
    ((hsearch_step_expand h_zero state head tail).pathOrder v).1 ≤ (state.pathOrder u).1 := by
  unfold hsearch_step_expand at v_head_after
  simp_all
  by_cases u_neq_v : u ≠ v
  · apply mergeSort_head_from_head_unsorted at v_head_after
    · specialize v_head_after u
      apply imp_iff_or_not.mp at v_head_after
      cases v_head_after
      case pos.inl p =>
        simp_all
        cases p
        case inl p =>
          split_ifs at p <;> (unfold hsearch_step_expand ; simp_all ; try grind)
        case inr p =>
          split_ifs at p
          all_goals
            unfold Nat.instFValueCompProd at p
            simp at p
            unfold hsearch_step_expand
            simp_all
            grind
      case pos.inr p =>
        apply absurd p
        clear p
        simp
        intro u_not_in_tail
        contradiction
    · intro a b c ab bc
      apply hsearch_merge_trans
      · apply ab
      · apply bc
    · intro a b
      apply hsearch_merge_total
  · simp at u_neq_v
    subst u_neq_v
    clear v_head_after
    unfold hsearch_step_expand
    simp_all
    split_ifs
    · rfl
    · rfl
    · grind

lemma dijkstra_new_head_cost_lt_other_on_stack_now
  (head : V) (tail : List V)
  (u : V) (u_on_stack_after : u ∈ (hsearch_step_expand h_zero state head tail).stack)
  (v : V) (after_not_nil : (hsearch_step_expand h_zero state head tail).stack ≠ [])
  (v_head_after : (hsearch_step_expand h_zero state head tail).stack.head after_not_nil = v):
  ((hsearch_step_expand h_zero state head tail).pathOrder v).1 ≤ ((hsearch_step_expand h_zero state head tail).pathOrder u).1 := by
    unfold hsearch_step_expand at v_head_after
    simp_all
    apply mergeSort_head_from_head_unsorted at v_head_after
    · specialize v_head_after u
      apply imp_iff_or_not.mp at v_head_after
      cases v_head_after
      case inl p =>
        cases p
        case inl eq =>
          subst eq
          rfl
        case inr p =>
          simp_all
          split_ifs at p
          all_goals
            unfold hsearch_step_expand
            unfold Nat.instFValueCompProd at p
            simp_all
            grind
      case inr p =>
        unfold hsearch_step_expand at u_on_stack_after
        simp_all
    · intro a b c ab bc
      apply hsearch_merge_trans
      · apply ab
      · apply bc
    · intro a b
      apply hsearch_merge_total

omit [DecidableEq V] in
private lemma track_walk_not_on_stack
  (on_stack_or_nei_visited : search_invar_on_stack_or_all_neighbours_visited state)
  (start_visited : search_invar_start_visited start state)
  (w_w : g.Walk start w)
  (w_nodup : w_w.support.Nodup)
  (no_pw_mem_on_stack : ∀ x ∈ w_w.support, x ∉ state.stack):
    ∀ x ∈ w_w.support, x ∈ state.visited := by
      cases w_w
      case nil =>
        intro x x_in_nil_supp
        simp_all
      case cons w' h p =>
        intro x x_in_supp
        unfold  Walk.support at x_in_supp
        apply List.mem_cons.mp at x_in_supp
        cases x_in_supp
        case inl x_is_start =>
          grind
        case inr x_in_p_support =>
          have p_nodup : p.support.Nodup := by
            unfold Walk.support at w_nodup
            apply List.nodup_cons.mp at w_nodup
            exact w_nodup.2
          apply track_walk_not_on_stack (w_w := p)
          · exact on_stack_or_nei_visited
          · unfold search_invar_start_visited at ⊢ start_visited
            unfold search_invar_on_stack_or_all_neighbours_visited at on_stack_or_nei_visited
            have start_not_on_stack : start ∉ state.stack := by
              apply no_pw_mem_on_stack
              unfold Walk.support
              simp
            specialize on_stack_or_nei_visited ⟨start, start_visited ⟩
            simp_all
          · exact p_nodup
          · intro y y_in_pp_supp
            apply no_pw_mem_on_stack
            unfold Walk.support
            apply List.mem_cons.mpr
            right
            apply y_in_pp_supp
          · apply x_in_p_support

omit [DecidableEq V] in
private lemma track_path_not_on_stack
  (on_stack_or_nei_visited : search_invar_on_stack_or_all_neighbours_visited state)
  (start_visited : search_invar_start_visited start state)
  (p_w : g.Path start w)
  (no_pw_mem_on_stack : ∀ x ∈ p_w.support, x ∉ state.stack):
    ∀ x ∈ p_w.support, x ∈ state.visited := by
      intro x x_in_supp
      apply track_walk_not_on_stack (w_w := p_w.val)
      · apply on_stack_or_nei_visited
      · apply start_visited
      · exact p_w.prop
      · intro y y_in_pw_supp
        apply no_pw_mem_on_stack
        apply y_in_pw_supp
      · apply x_in_supp

/--
  The node v is the head of the stack after this expansion.
  I.e. it is smaller than all other nodes on the stack, after the expansion.
  v has a mother (the_mother). There is a path from start to the_mother, that is a shortest path.
  the_mother is visited, but is not on the stack or was the head.
  Notably, this implies that the pathOrder of the_mother is the cost of that path.


  In addition, we have a path p' that is supposedly shorter than the path start->the_mother->v
  Now, p' contains a first node u that is still on the stack (this lemma only treats this case, if not use other lemma)
  We can now consider the sub-path of p' from start to u

-/
private lemma dijkstra_shorter_path_first_on_stack_not_head {start : V}
(the_mother : V)
(v : V)
(u : V)
(start_visited : search_invar_start_visited start state)
(on_stack_or_nei_visited : search_invar_on_stack_or_all_neighbours_visited state)
(update_invar : hsearch_invar_on_stack_or_all_neighbours_max_order state)
(start_not_mem_tail : search_invar_start_not_mem_tail start state)
(head : V)
(tail : List V)
(prior_invar : dijkstra_stack_shortest_path start state)
(compose : state.stack = head :: tail)
(adj_mother_v : g.Adj the_mother v)
(path_mother : Path start the_mother)
----
(v_not_in_mother_path : v ∉ path_mother.val.support)
(path_mother_v : Path start v)
(path_mother_v_is : path_mother_v = path_mother.concat adj_mother_v v_not_in_mother_path)
------ p' is the supposedly shorter path
(p' : g.Path start v)
(p'_cheaper : p'.val.cost < path_mother_v.val.cost)
--
(u_in_support : u ∈ p'.val.support)
(u_on_stack : u ∈ state.stack)
(u_ne_v : u ≠ v)
(prior_not_on_stack : ((List.takeWhile (fun x => decide (x ≠ u)) p'.support).all fun x => decide (x ∉ state.stack)) = true)
(u_visited : u ∈ state.visited)
(su : g.Path start u)
(cheaper : su.cost ≤ p'.cost)
(u_ne_head : head ≠ u)
(mother_plus_e_le_u : path_mother.cost + g.edgeCost adj_mother_v ≤ (state.pathOrder u).1 )
:
⊥ := by
  let e := g.edgeCost adj_mother_v
  obtain ⟨su, cheaper, supp_subseq⟩ := p'.contains_subpath_cost u_in_support u_ne_v

  -- u cannot be the start node (as u has to be on the stack and cannot be head)
  have u_ne_start : start ≠ u := by
    by_contra
    subst this
    --simp_all
    simp [*] at u_on_stack
    cases u_on_stack
    · grind
    · next start_in_tail =>
      unfold search_invar_start_not_mem_tail at start_not_mem_tail
      grind

  -- this allows us to consider the predecessor of u on the path su - which we call w
  obtain ⟨ w,p_w,adj_w_u,u_not_earlier_in_path,su_compose⟩ := su.split_at_end u_ne_start

  have no_pw_mem_on_stack : ∀ x ∈ p_w.support, x ∉ state.stack := by
    intro x x_in_support
    unfold Path.support at prior_not_on_stack supp_subseq
    rw [su_compose] at supp_subseq
    simp at supp_subseq
    unfold List.IsPrefix at supp_subseq
    obtain ⟨ t, compose ⟩ := supp_subseq
    rw [← compose] at prior_not_on_stack
    rw [List.append_assoc] at prior_not_on_stack
    rw [List.takeWhile_append_of_pos] at prior_not_on_stack
    · rw [List.all_append] at prior_not_on_stack
      apply Bool.and_elim_left at prior_not_on_stack
      apply List.all_iff_forall_prop.mp at prior_not_on_stack
      apply prior_not_on_stack
      apply x_in_support
    · grind

  -- w now has to not be part of the stack (as u was the first node to be on the stack!)
  have w_not_on_stack : w ∉ state.stack := by
    apply no_pw_mem_on_stack
    apply Walk.goal_in_support

  have w_visited : w ∈ state.visited := by
    apply track_path_not_on_stack (p_w := p_w)
    · exact on_stack_or_nei_visited
    · exact start_visited
    · exact no_pw_mem_on_stack
    · apply Path.goal_in_support

  let f := edgeCost adj_w_u
  have p_w_le_su : p_w.cost + f = su.cost := by
    conv => right ; unfold Path.cost
    rw [su_compose]
    unfold f
    rw [add_comm]
    rw [Walk.concat_inc_cost_by_edge]
    rfl
  -- Eq 8
  have du_le_sq_f : (state.pathOrder u).1 ≤ p_w.cost + f := by
    unfold dijkstra_stack_shortest_path at prior_invar
    specialize prior_invar w w_visited
    --simp_all
    unfold cost_is at prior_invar
    rw [or_imp] at prior_invar
    obtain ⟨prior_invar, _ ⟩ := prior_invar
    specialize prior_invar w_not_on_stack
    obtain ⟨ sp, cost_is_order,is_cheapest ⟩ := prior_invar
    unfold Path.is_cheapest at is_cheapest
    specialize is_cheapest p_w
    conv at is_cheapest => right ; unfold Path.cost
    have w_sp : (state.pathOrder w).1 ≤ p_w.val.cost := by omega
    apply le_trans
    rotate_left
    · apply add_le_add_left
      apply w_sp
    · unfold hsearch_invar_on_stack_or_all_neighbours_max_order at update_invar
      specialize update_invar ⟨ w, w_visited ⟩ w_not_on_stack u adj_w_u
      omega

  have p'_lt_mp_plus_e : p'.cost < path_mother.cost + e := by
    unfold Path.cost
    convert p'_cheaper
    rw [path_mother_v_is]
    unfold Path.concat
    simp [Walk.concat_inc_cost_by_edge]
    grind

  have p'_lt_du : p'.cost < (state.pathOrder u).1 := by omega
  have p'_lt_sw_f : p'.cost < p_w.cost + f := by omega

  omega

private lemma dijkstra_shorter_path_with_optimal_node_and_adj_on_stack
  {s v : V}
  (p : g.Path s v)
  (head : V)
  (tail : List V)
  (compose : state.stack = head :: tail)
  (update_invar : hsearch_invar_on_stack_or_all_neighbours_max_order state)
  (p_path_cost : p.val.cost ≤ ((hsearch_step_expand h_zero state head tail).pathOrder v).1)
  (stack_not_empty_after : ¬(hsearch_step_expand h_zero state head tail).stack = [])
  (head_after_is_v : (hsearch_step_expand h_zero state head tail).stack.head stack_not_empty_after = v)
  -- p' is a shorter path
  (p' : g.Path s v)
  (p'_cheaper : p'.val.cost < p.val.cost)
  -- two nodes on p'
  (u u' : V)
  (u_visited : u ∈ state.visited)
  (u_not_in_stack_tail: u ∉ state.stack.tail)
  (u'_visited : u' ∈ state.visited)
  (u'_on_stack : u' ∈ state.stack)
  (u'_ne_head : u' ≠ head)
  (adj_u_u' : g.Adj u u')
  (p'_u : g.Walk s u)
  (p'_u_edge_le_p' : (p'_u.concat adj_u_u').cost ≤ p'.val.cost)
  (u_cost_is : g.cost_is s u (state.pathOrder u).1)
: ⊥ := by

  -- w is on stack and must thus be larger
  have h4 : ((hsearch_step_expand h_zero state head tail).pathOrder v).1 ≤  ((hsearch_step_expand h_zero state head tail).pathOrder u').1:= by
    apply dijkstra_new_head_cost_lt_other_on_stack_now
    · unfold hsearch_step_expand ; simp ; grind
    · apply head_after_is_v

  -- state order of w can only have decreased by expansion (as it was visited before)
  have h5: ((hsearch_step_expand h_zero state head tail).pathOrder u').1 ≤ (state.pathOrder u').1 := by
    unfold hsearch_step_expand ; simp ; grind

  have h6 : ((hsearch_step_expand h_zero state head tail).pathOrder u').1 ≤ p'.val.cost := by
    apply le_trans ; rotate_left
    · apply p'_u_edge_le_p'
    · unfold cost_is at u_cost_is
      obtain ⟨shortest, shortest_eq_pathOrder, is_cheapest ⟩ := u_cost_is
      unfold Path.is_cheapest at is_cheapest
      rw [shortest_eq_pathOrder] at is_cheapest
      clear shortest shortest_eq_pathOrder
      --have w_sp : (state.pathOrder w).1 ≤ p_w.val.cost := by omega
      apply le_trans
      rotate_left
      · simp
        apply add_le_add_right

        obtain ⟨cp, sp_cheaper ⟩ := p'_u.cheaper_path_exists
        apply le_trans --; rotate_left
        · apply is_cheapest cp
        · apply sp_cheaper
      · unfold hsearch_invar_on_stack_or_all_neighbours_max_order at update_invar
        by_cases u_eq_head : u = head
        · unfold hsearch_step_expand
          simp
          grind
        · apply le_trans
          · apply h5
          · specialize update_invar ⟨ u, u_visited ⟩ (by grind) u' adj_u_u'
            simp only at update_invar
            rw [add_comm]
            exact update_invar

  ---- path order of w was updated when expanding its predecessors, who is
  omega

private lemma dijkstra_shorter_path_via_head
      (start : V)
      (on_stack_or_nei_visited : search_invar_on_stack_or_all_neighbours_visited state)
      (stack_visited_invar : search_invar_stack_is_visited state)
      (update_invar : hsearch_invar_on_stack_or_all_neighbours_max_order state)
      (stack_nodup : search_invar_stack_nodup state)
      (head : V)
      (tail : List V)
      (prior_invar : dijkstra_stack_shortest_path start state)
      (compose : state.stack = head :: tail)
      (v : V)
      (v_visited_after : v ∈ (hsearch_step_expand h_zero state head tail).visited)
      (head_was_visited_before : head ∈ state.visited)
      (stack_not_empty_after : ¬(hsearch_step_expand h_zero state head tail).stack = [])
      (head_after_is_v : (hsearch_step_expand h_zero state head tail).stack.head stack_not_empty_after = v)
      (the_mother : V)
      (path_mother : g.Path start the_mother)
      (path_mother_v : g.Path start v)
      (p' : g.Path start v)
      (p'_cheaper : p'.val.cost < path_mother_v.val.cost)
      (h2' : path_mother_v.val.cost ≤ ((hsearch_step_expand h_zero state head tail).pathOrder v).1)
      (u : V)
      (u_in_support : u ∈ p'.val.support)
      (u_on_stack : u ∈ state.stack)
      (u_ne_v : u ≠ v)
      (u_visited : u ∈ state.visited)
      (su : g.Path start u)
      (cheaper : su.cost ≤ p'.cost ∧ su.support <+: p'.support)
      (u_eq_head : head = u):
    ⊥ := by
          subst u_eq_head
          obtain ⟨u',s_u,adj_head_u',u'_v,supp1,supp2,compose⟩  := Path.recompose p' u_in_support u_ne_v
          have compose_early_split : p'.val = s_u.val.append (Walk.cons adj_head_u' u'_v) := by
            rw [compose]
            unfold Path.concat Path.append
            simp
            apply Walk.internal_contact_to_cons_walk

          have u'_ne_start : u' ≠ start := by
            by_contra
            rw [this] at supp1
            simp at supp1

          have u'_ne_head : u' ≠ head := by
            by_contra ; subst this
            apply absurd (s_u.val.goal_in_support) supp1

          have p'_cost_compose : p'.val.cost = s_u.val.cost + u'_v.val.cost + g.edgeCost adj_head_u' := by
            rw [compose]
            unfold Path.append Path.concat
            simp only [Walk.append_cost, Walk.concat_inc_cost_by_edge]
            omega

          --rw [p'_cost_compose] at p'_cheaper
          -- w is on the stack and will remain on the stack
          have h3 : s_u.val.cost + edgeCost adj_head_u' + u'_v.val.cost < ((hsearch_step_expand h_zero state head tail).pathOrder v).1 := by omega

          have h3' : p'.val.cost < ((hsearch_step_expand h_zero state head tail).pathOrder v).1 := by omega


          by_cases v_not_u' : v ≠ u'
          · by_cases u'_visited : u' ∈ state.visited
            · by_cases u'_not_on_stac : u' ∉ state.stack
              · have u'_v_elem_on_stack_or_v_visited :
                  -- possibly stronger: the all elements are also visited!
                  (∃ w ∈ u'_v.val.support, w ∈ state.stack ∧ w ≠ v ∧ (u'_v.support.takeWhile (· ≠ w)).all (· ∉ state.stack)) ∨
                    (v ∈ state.visited ∧ ∀ w ∈ u'_v.val.support, w ≠ v → w ∉ state.stack ∧ w ∈ state.visited) :=
                  run_path_through_state_yields_node_on_stack_or_all_visited u' v v_not_u' u'_v state u'_visited on_stack_or_nei_visited


                cases u'_v_elem_on_stack_or_v_visited
                · rename_i h
                  obtain ⟨w,w_in_u'_v_support,w_on_stack,w_ne_v,all_prior_not_on_stack⟩ := h
                  obtain ⟨ u'_w, cheaper, supp_subseq ⟩ := u'_v.contains_subpath_cost w_in_u'_v_support w_ne_v

                  have head_ne_w : head ≠ w := by
                    by_contra ; subst this
                    have p'_supp_compose: p'.val.support = s_u.val.support ++ u'_v.val.support := by
                      rw [compose_early_split]
                      rw [Walk.support_of_append]
                      conv =>
                        left
                        arg 2
                        unfold Walk.support
                      simp only [List.tail_cons]
                    have head_in_su_supp : head ∈ s_u.val.support := by simp
                    --have head_in_u'v_supp : head ∈ u'_v.support := by unfold Path.support ; exact w_in_u'_v_support
                    have p'_nodup := p'.prop
                    rw [p'_supp_compose] at p'_nodup
                    apply List.nodup_append.mp at p'_nodup
                    obtain ⟨_,_,contra⟩ := p'_nodup
                    specialize contra head head_in_su_supp head w_in_u'_v_support
                    simp only [ne_eq, not_true_eq_false] at contra

                  have u'_ne_w : u' ≠ w := by
                    by_contra ; subst this ; contradiction

                    --obtain ⟨before_w, _ ⟩ := u'_w.split_at_end head_ne_w
                  obtain ⟨ before_w, u'_before_w, adj_bef_w_w, w_not_in_supp, u'_w_compose⟩ := u'_w.split_at_end u'_ne_w

                  have no_pw_mem_on_stack : ∀ x ∈ u'_before_w.support, x ∉ state.stack := by
                    intro x x_in_support
                    unfold Path.support at all_prior_not_on_stack supp_subseq
                    rw [u'_w_compose] at supp_subseq
                    simp at supp_subseq
                    unfold List.IsPrefix at supp_subseq
                    obtain ⟨ t, compose ⟩ := supp_subseq
                    rw [← compose] at all_prior_not_on_stack
                    rw [List.append_assoc] at all_prior_not_on_stack
                    rw [List.takeWhile_append_of_pos] at all_prior_not_on_stack
                    · rw [List.all_append] at all_prior_not_on_stack
                      apply Bool.and_elim_left at all_prior_not_on_stack
                      apply List.all_iff_forall_prop.mp at all_prior_not_on_stack
                      apply all_prior_not_on_stack
                      unfold Path.support at x_in_support
                      apply x_in_support
                    · grind

                  -- w now has to not be part of the stack (as u was the first node to be on the stack!)
                  have before_w_not_on_stack : before_w ∉ state.stack := by
                    apply no_pw_mem_on_stack
                    apply Walk.goal_in_support

                  have before_w_visited : before_w ∈ state.visited := by
                    apply track_path_not_on_stack (p_w := u'_before_w)
                    · exact on_stack_or_nei_visited
                    · unfold search_invar_start_visited
                      exact u'_visited
                    · exact no_pw_mem_on_stack
                    · apply Path.goal_in_support

                  have w_visited : w ∈ state.visited := by
                    unfold search_invar_on_stack_or_all_neighbours_visited at on_stack_or_nei_visited
                    specialize on_stack_or_nei_visited ⟨ before_w, before_w_visited ⟩
                    grind


                  let start_before_w : g.Walk start before_w := (s_u.val.concat adj_head_u').append u'_before_w.val

                  apply dijkstra_shorter_path_with_optimal_node_and_adj_on_stack (p:=path_mother_v) (p':=p') (p'_u:=start_before_w) (u:=before_w) (u':=w)  <;> try assumption
                  · grind
                  · apply head_ne_w.symm
                  · rw [p'_cost_compose]
                    unfold start_before_w
                    have u'_v_cost : edgeCost adj_bef_w_w + u'_before_w.val.cost ≤ u'_v.val.cost := by
                      unfold Path.cost at cheaper
                      apply le_trans ; rotate_left
                      · apply cheaper
                      · rw [u'_w_compose]
                        simp
                    simp
                    omega
                  · unfold dijkstra_stack_shortest_path at prior_invar
                    specialize prior_invar before_w before_w_visited
                    simp [before_w_not_on_stack] at prior_invar
                    exact prior_invar

                -- entire path is visited and not on the stack (now all nodes on p' except for head itself)
                · -- path was fully on not stack and fully visited
                  rename_i h
                  obtain ⟨v_visited,all_except_v_not_on_stack_and_visited⟩ := h


                  obtain ⟨ last,path_u'_last,last_adj_v,v_not_earlier_in_path,u'_v_compose⟩ := u'_v.split_at_end (Ne.symm v_not_u')

                  have last_in_u'_v : last ∈ u'_v.val.support := by simp_all
                  have last_ne_v : last ≠ v := by
                    by_contra w_eq_v
                    rw [← w_eq_v] at v_not_earlier_in_path
                    have w_in_supp : last ∈ path_u'_last.val.support := Path.goal_in_support path_u'_last
                    contradiction

                  have last_not_mem_stack : last ∉ state.stack := by grind
                  have last_visited : last ∈ state.visited := by grind

                  by_cases last_eq_head : last = head
                  · rename_i stack_compose
                    rw [stack_compose] at last_not_mem_stack
                    grind
                  · rename last ≠ head => last_ne_head

                    -- last is visited, but not on stack, no must have been expanded
                    have last_expanded : (state.pathOrder last).1 + edgeCost last_adj_v ≥ (state.pathOrder v).1 := by
                      specialize update_invar ⟨last, last_visited⟩ last_not_mem_stack v last_adj_v
                      exact update_invar

                    let w_start_last : g.Walk start last := (s_u.val.concat adj_head_u').append path_u'_last

                    -- w_start_last must be longer than the path order of last
                    have w_start_last_ge_order_last : w_start_last.cost ≥ (state.pathOrder last).1 := by
                      specialize prior_invar last last_visited
                      simp [last_not_mem_stack] at prior_invar
                      unfold cost_is at prior_invar
                      obtain ⟨p,p_eq,p_cheapest ⟩ := prior_invar
                      unfold Path.is_cheapest at p_cheapest
                      obtain ⟨ p'', p''_leq_w_s_l⟩ := w_start_last.cheaper_path_exists
                      apply le_trans ; rotate_left
                      · exact p''_leq_w_s_l
                      · specialize p_cheapest p''
                        grind


                    have path_via_gt_order_v : w_start_last.cost + edgeCost last_adj_v ≥ (state.pathOrder v).1 := by omega


                    have path_via_le_p' : w_start_last.cost + edgeCost last_adj_v = p'.val.cost := by
                      rw [compose]
                      unfold w_start_last
                      unfold Path.concat Path.append
                      simp
                      rw [u'_v_compose]
                      simp
                      grind


                    have p'_geq_order_v : p'.val.cost  ≥ (state.pathOrder v).1 := by omega

                    have hh : (state.pathOrder v).1 ≥ ((hsearch_step_expand h_zero state head tail).pathOrder v).1 := by
                      unfold hsearch_step_expand ; simp ; grind

                    omega
              ·
                apply dijkstra_shorter_path_with_optimal_node_and_adj_on_stack (p:=path_mother_v) (p':=p')  (p'_u:=s_u.val) (u:=head) (u':=u')  <;> try assumption
                · by_contra head_in_tail
                  have head_after_on_stack : head ∈ (hsearch_step_expand h_zero state head tail).stack := by
                    unfold hsearch_step_expand ; simp ; grind

                  -- strange impossible case: head is twice on the stack. This should be impossible.
                  -- unclear how.
                  specialize stack_nodup head
                  rename_i stack_compose
                  rw [stack_compose] at stack_nodup head_in_tail
                  simp at stack_nodup head_in_tail
                  apply List.count_eq_zero.mp at stack_nodup
                  contradiction
                · simp at u'_not_on_stac
                  exact u'_not_on_stac
                · rw [p'_cost_compose]
                  simp
                  omega
                · unfold dijkstra_stack_shortest_path at prior_invar
                  specialize prior_invar head (by grind)
                  rename_i _ _ stack_compose
                  rw [stack_compose] at prior_invar

                  simp at prior_invar
                  exact prior_invar
            · -- u' will be on stack afterwards
              -- as u' ≠ v, it must have a path order ≥v, i.e. the update from head cause a value larger than the length of path_mover_v -- which contradicts shortestpath
              have u'_on_stack_after : u' ∈ (hsearch_step_expand h_zero state head tail).stack := by
                unfold hsearch_step_expand ; simp ; grind

              have u'_larger_order : ((hsearch_step_expand h_zero state head tail).pathOrder v).1 ≤ ((hsearch_step_expand h_zero state head tail).pathOrder u').1 := by
                apply dijkstra_new_head_cost_lt_other_on_stack_now <;> try assumption

              --have x2 : s_u.val.cost + edgeCost adj_head_u' + u'_v.val.cost < ((hsearch_step_expand h_zero state head tail).pathOrder u').1 := by omega


              have updated_from_head : ((hsearch_step_expand h_zero state head tail).pathOrder u').1 ≤ (state.pathOrder head).1 + edgeCost adj_head_u' := by
                unfold hsearch_step_expand ; simp ; grind

              have head_optimal : s_u.val.cost ≥ (state.pathOrder head).1 := by
                specialize prior_invar head head_was_visited_before
                rename_i stack_compose
                rw [stack_compose] at prior_invar
                simp at prior_invar
                unfold cost_is at prior_invar
                obtain ⟨p,p_cost,is_cheapest⟩ := prior_invar
                unfold Path.is_cheapest at is_cheapest
                specialize is_cheapest s_u
                rw [p_cost] at is_cheapest
                unfold Path.cost at is_cheapest
                exact is_cheapest

              omega
          · simp at v_not_u' ; subst v_not_u'
            -- p' goes to head and then immediately to v
            have u'_v_cost_zero : u'_v.cost = 0 := by apply WeightedDiGraph.Path.cost_empty_zero
            unfold Path.cost at u'_v_cost_zero
            simp [u'_v_cost_zero] at p'_cost_compose h3
            -- v has been updated from head
            have  v_updated : ((hsearch_step_expand h_zero state head tail).pathOrder v).1 ≤ (state.pathOrder head).1 + edgeCost adj_head_u' := by
              unfold hsearch_step_expand ; simp ; grind
            have  head_optimal : (state.pathOrder head).1 ≤ s_u.val.cost := by
              unfold dijkstra_stack_shortest_path at prior_invar
              specialize prior_invar head (by grind)
              rename_i _ _ stack_compose
              rw [stack_compose] at prior_invar
              simp at prior_invar
              unfold cost_is at prior_invar
              obtain ⟨sp, cost_eq, cheapest⟩ := prior_invar
              unfold Path.is_cheapest at cheapest
              specialize cheapest s_u
              rw [cost_eq] at cheapest
              unfold Path.cost at cheapest
              exact cheapest
            omega


lemma dijkstra_path_head_adj_new_head_is_cheapest {start : V}
    (start_visited : start ∈ state.visited)
    (stack_visited_invar : WeightedDiGraph.search_invar_stack_is_visited state)
    (on_stack_or_nei_visited : search_invar_on_stack_or_all_neighbours_visited state)
    (update_invar : hsearch_invar_on_stack_or_all_neighbours_max_order state)
    (prior_invar : dijkstra_stack_shortest_path start state)
    (start_not_mem_tail : search_invar_start_not_mem_tail start state)
    (stack_nodup : search_invar_stack_nodup state)
    -- execution of current step
    {head : V} {tail : List V}
    (compose : state.stack = head :: tail)
    (head_was_visited_before : head ∈ state.visited)
    (path_to_head : g.Path start head)
    (ph_eq_dh : path_to_head.cost = (state.pathOrder head).1)
    -- the new head of the stack --
    (v : V)
    (v_not_start : v ≠ start)
    (stack_not_empty_after : ¬(hsearch_step_expand h_zero state head tail).stack = [])
    (head_after_is_v : (hsearch_step_expand h_zero state head tail).stack.head stack_not_empty_after = v)
    (adj_head_v : g.Adj head v)
    (v_order_eq_head_plus_edge : ((hsearch_step_expand h_zero state head tail).pathOrder v).1 = ((hsearch_step_expand h_zero state head tail).pathOrder head).1 + g.edgeCost adj_head_v)
    (support_visited : ∀ u ∈ path_to_head.val.support, u ∈ state.visited)
    (v_not_in_support_ph : v ∉ path_to_head.val.support)
    (path_explored_contra : ∀ p : g.Path start v, (p.cost < (path_to_head.concat adj_head_v v_not_in_support_ph).cost ∧ v ∈ state.visited ∧ ∀ u ∈ p.support, u ≠ v → u ∉ state.stack ∧ u ∈ state.visited) → ⊥)
    --(path_explored_contra_head : ∀ w : V, w ≠ head → ∀ adj_h_w : g.Adj head w, ∀ p : g.Path w v, (p.cost + g.edgeCost adj_h_w < g.edgeCost adj_head_v ∧ v ∈ state.visited ∧ ∀ u ∈ p.support, u ≠ v → u ∉ state.stack ∧ u ∈ state.visited) → ⊥)
    :
    (path_to_head.concat adj_head_v v_not_in_support_ph).is_cheapest := by
      let path_to_v := path_to_head.concat adj_head_v v_not_in_support_ph
      let e := g.edgeCost adj_head_v

      -- Situation: v is head of stack after expansion of head
      -- v was added to the stack due to expansion of v (i.e. it was not visited before)
      -- ph (path_to_head) is a shortest path to head
      -- selected apth to v is (path_to_head ; <head,v>)
      --
      -- Now: Assume there is a shorter path to v: p'
      unfold Path.is_cheapest
      intro p'
      by_contra p'_is_cheaper
      simp at p'_is_cheaper


      -- we can run along p' until we find a first node in p' that is still on the stack (before the expansion)
      -- or (second case) no node is on the stack, but then all nodes are visited
      have p'_elem_on_stack_or_v_visited :
        -- possibly stronger: the all elements are also visited!
        (∃ u ∈ p'.val.support, u ∈ state.stack ∧ u ≠ v ∧ (p'.support.takeWhile (· ≠ u)).all (· ∉ state.stack)) ∨
          (v ∈ state.visited ∧ ∀ u ∈ p'.val.support, u ≠ v → u ∉ state.stack ∧ u ∈ state.visited) :=
        run_path_through_state_yields_node_on_stack_or_all_visited start v v_not_start p' state start_visited on_stack_or_nei_visited
      -- p' must be cheaper than the cost of path_to_v -- which is path_to_head.cost + e (by construction)
      -- Eq 1: by expand p'_is_cheaper
      have su_lt_sh_e : p'.cost < path_to_head.cost + e := by
        unfold Path.cost
        convert p'_is_cheaper
        unfold Path.concat
        simp_all only [Walk.start_in_support, search_invar_stack_is_visited, List.mem_cons, forall_eq_or_imp, true_and,search_invar_on_stack_or_all_neighbours_visited, Subtype.forall, not_or, and_imp, Walk.goal_in_support,Path.cost_same, ne_eq, Path.support, «Prop».bot_eq_false, imp_false, not_and, not_forall, decide_not, Bool.decide_and, List.all_eq_true, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true,decide_eq_false_iff_not, Walk.concat_inc_cost_by_edge]
        rw [add_comm]
      -- we set the pathCost of v to exactly this value
      have v_after_eq_e_sh: ((hsearch_step_expand h_zero state head tail).pathOrder v).1 = e + path_to_head.cost := by
        unfold hsearch_step_expand
        unfold e
        --simp_all
        rw [add_comm]
        simp
        split_ifs
        · rename_i _ v_visited lt
          unfold hsearch_step_expand at v_order_eq_head_plus_edge
          simp_all
          grind
        · simp_all
        · simp_all
        · simp_all
        · simp_all

      cases p'_elem_on_stack_or_v_visited
      · next u_in_support_on_stack =>
        -- first node in p that is on the stack: call it u
        -- all nodes before u are not on the stack, i.e. paths to them are shortest paths.
        obtain ⟨u, ⟨u_in_support, ⟨ u_on_stack, u_ne_v, prior_not_on_stack⟩ ⟩ ⟩ := u_in_support_on_stack
        have u_visited : u ∈ state.visited := by grind
        -- extract path from start to this node u
        -- su is not longer than p' itself
        -- cheaper is Eq 5. (su) ≤ p'
        obtain ⟨ su, cheaper⟩ := p'.contains_subpath_cost u_in_support u_ne_v

        by_cases u_ne_head : head ≠ u
        · -- Eq 2: v is now the stack head
          have e_sh_le_du : e + path_to_head.cost ≤ (state.pathOrder u).1 := by
            rw [← v_after_eq_e_sh]
            apply dijkstra_new_head_cost_lt_other_on_stack_before
            · exact compose
            · exact u_on_stack
            · exact u_ne_head.symm
            · grind
            · exact adj_head_v
            · apply head_after_is_v
          -- Eq 6: d(h) ≤ d(u) (from h being the stack head)
          --have dh_le_du : (state.pathOrder head).1 ≤ (state.pathOrder u).1 := by

          --have su_lt_sh_e : su.cost < path_to_head.cost + e := by omega
          apply dijkstra_shorter_path_first_on_stack_not_head (the_mother:=head) (v:=v) (u:=u) (start:=start) <;> try assumption
          · rfl
          · exact cheaper.1
          · grind

        · simp at u_ne_head
          apply dijkstra_shorter_path_via_head (start:=start) (v:=v) (the_mother:=head) <;> try assumption
          · unfold hsearch_step_expand
            simp
            grind
          ·
            unfold Path.concat
            simp only [Walk.concat_inc_cost_by_edge]
            unfold e Path.cost at v_after_eq_e_sh
            apply le_of_eq
            exact v_after_eq_e_sh.symm
      · next h =>
        have v_visited := h.left
        specialize path_explored_contra p'
        simp_all




lemma dijkstra_path_mother_adj_new_head_is_cheapest {start : V}
    (mother_invar : search_invar_mother_is_visited state)
    (mother_invar_adj : search_invar_mother_is_adjacent start state)
    (decreasing_invar : search_invar_mother_decreasing_path_order start state)
    (start_visited : search_invar_start_visited start state)
    (on_stack_or_nei_visited : search_invar_on_stack_or_all_neighbours_visited state)
    (stack_visited_invar : search_invar_stack_is_visited state)
    (path_order_diff : hsearch_path_order_diff_by_edge_cost start state)
    (update_invar : hsearch_invar_on_stack_or_all_neighbours_max_order state)
    (start_not_mem_tail : search_invar_start_not_mem_tail start state)
    (stack_nodup : search_invar_stack_nodup state)
    (head : V)
    (tail : List V)
    (prior_invar : dijkstra_stack_shortest_path start state)
    (compose : state.stack = head :: tail)
    (v : V)
    (v_visited_after : v ∈ (hsearch_step_expand h_zero state head tail).visited)
    (head_was_visited_before : head ∈ state.visited)
    (path_to_head : g.Path start head)
    (v_not_start : v ≠ start)
    (stack_not_empty_after : ¬(hsearch_step_expand h_zero state head tail).stack = [])
    (head_after_is_v : (hsearch_step_expand h_zero state head tail).stack.head stack_not_empty_after = v)
    (the_mother : V)
    (mother_visited : the_mother ∈ state.visited)
    (pathOrder_unchanged : (hsearch_step_expand h_zero state head tail).pathOrder v = state.pathOrder v)
    (adj_mother_v : g.Adj the_mother v)
    (mother_and_edge_smaller_order_before : (state.pathOrder the_mother).1 + edgeCost adj_mother_v ≤ (state.pathOrder v).1)
    (mother_not_on_stack : the_mother ∉ state.stack)
    (path_mother : Path start the_mother)
    (path_mother_is : path_mother = (extract_path_to start the_mother state mother_visited mother_invar mother_invar_adj decreasing_invar).fst)
    (v_not_in_mother_path : v ∉ path_mother.val.support)
    (path_mother_v : Path start v)
    (path_mother_v_is : path_mother_v = path_mother.concat adj_mother_v v_not_in_mother_path)
    (path_explored_contra : ∀ p : g.Path start v, (p.cost < (path_mother.concat adj_mother_v v_not_in_mother_path).cost ∧ v ∈ state.visited ∧ ∀ u ∈ p.support, u ≠ v → u ∉ state.stack ∧ u ∈ state.visited) → ⊥)
    (p' : g.Path start v)
    (p'_cheaper : p'.val.cost < path_mother_v.val.cost):
    ⊥ := by


      -- we can run along p' until we find a first node in p' that is still on the stack (before the expansion)
      -- or (second case) no node is on the stack, but then all nodes are visited
      have p'_elem_on_stack_or_v_visited :
        -- possibly stronger: the all elements are also visited!
        (∃ u ∈ p'.val.support, u ∈ state.stack ∧ u ≠ v ∧ (p'.support.takeWhile (· ≠ u)).all (· ∉ state.stack)) ∨
          (v ∈ state.visited ∧ ∀ u ∈ p'.val.support, u ≠ v → u ∉ state.stack ∧ u ∈ state.visited) :=
        run_path_through_state_yields_node_on_stack_or_all_visited start v v_not_start p' state start_visited on_stack_or_nei_visited

      have h1 : path_mother.cost + edgeCost adj_mother_v ≤ (state.pathOrder v).1:= by
        convert mother_and_edge_smaller_order_before
        apply eq_of_le_of_ge
        · rw [path_mother_is]
          apply hsearch_path_extracted_not_longer_than_path_order
          exact path_order_diff
        · unfold dijkstra_stack_shortest_path at prior_invar
          specialize prior_invar the_mother mother_visited
          simp [mother_not_on_stack] at prior_invar
          unfold cost_is at prior_invar
          obtain ⟨ p, ⟨order, is_cheapest⟩ ⟩ := prior_invar
          rw [← order]
          unfold Path.is_cheapest at is_cheapest
          exact is_cheapest path_mother
      have h2 : path_mother.cost + edgeCost adj_mother_v ≤ ((hsearch_step_expand h_zero state head tail).pathOrder v).1 := by
        rw [pathOrder_unchanged]
        apply h1

      have h2' : path_mother_v.val.cost ≤ ((hsearch_step_expand h_zero state head tail).pathOrder v).1 := by
        rw [path_mother_v_is]
        unfold Path.concat
        unfold Path.cost at h2
        simp
        rw [add_comm]
        exact h2


      cases p'_elem_on_stack_or_v_visited
      · next u_in_support_on_stack =>
        -- first node in p that is on the stack: call it u
        -- all nodes before u are not on the stack, i.e. paths to them are shortest paths.
        obtain ⟨u, ⟨u_in_support, ⟨ u_on_stack, u_ne_v, prior_not_on_stack⟩ ⟩ ⟩ := u_in_support_on_stack
        have u_visited : u ∈ state.visited := by grind
        -- extract path from start to this node u
        -- su is not longer than p' itself
        obtain ⟨su, cheaper⟩ := p'.contains_subpath_cost u_in_support u_ne_v

        by_cases u_ne_head : head ≠ u
        ·
          apply dijkstra_shorter_path_first_on_stack_not_head (the_mother:=the_mother) (v:=v) (u:=u) (start:=start) <;> try assumption
          · exact cheaper.1
          ·
            have h3 : ((hsearch_step_expand h_zero state head tail).pathOrder v).1 ≤ ((hsearch_step_expand h_zero state head tail).pathOrder u).1 := by
              apply dijkstra_new_head_cost_lt_other_on_stack_now
              · unfold hsearch_step_expand
                simp
                rw [compose] at u_on_stack
                rw [List.mem_cons] at u_on_stack
                cases u_on_stack
                case inl u_eq_head =>
                  apply absurd u_eq_head.symm u_ne_head
                case inr u_tail =>
                  left ; assumption
              · apply head_after_is_v
            have h4 : ((hsearch_step_expand h_zero state head tail).pathOrder u).1 ≤ (state.pathOrder u).1 := by
              unfold hsearch_step_expand
              simp
              grind

            have h5 : ((hsearch_step_expand h_zero state head tail).pathOrder v).1 ≤ (state.pathOrder u).1 := by omega

            omega
        · simp at u_ne_head
          rename head = u => u_eq_head
          apply dijkstra_shorter_path_via_head (start:=start) (v:=v) (the_mother:=the_mother) <;> try assumption
      -- 2. case: all nodes in p' are visited and all but v are not on the stack
      · next h =>
        -- path is completely explored, so we have the update invar along it
        have v_visited := h.left
        specialize path_explored_contra p'
        simp_all


set_option maxHeartbeats 2000000000 in
lemma dijkstra_expand_keeps_shortest_path_invar
    (start : V) (goal : V)
    ----- co-invariants needed for path extraction
    (mother_invar : WeightedDiGraph.search_invar_mother_is_visited state)
    (mother_invar_adj : WeightedDiGraph.search_invar_mother_is_adjacent start state)
    (decreasing_invar : WeightedDiGraph.search_invar_mother_decreasing_path_order start state)
    (start_visited : WeightedDiGraph.search_invar_start_visited start state)
    (on_stack_or_nei_visited : WeightedDiGraph.search_invar_on_stack_or_all_neighbours_visited state)
    (stack_visited_invar : WeightedDiGraph.search_invar_stack_is_visited state)
    -- new bfs_ specific invars
    (path_order_diff : hsearch_path_order_diff_by_edge_cost start state)
    --(extract_length_invar : dijkstra_path_as_extracted_as_long_as_sort_index start state)
    (update_invar : hsearch_invar_on_stack_or_all_neighbours_max_order state)
    (start_path_order : hsearch_invar_start_path_order_zero_zero start state)
    (start_not_mem_tail : search_invar_start_not_mem_tail start state)
    (stack_nodup : search_invar_stack_nodup state)
    :
     ∀ head : V, ∀ tail : List V,
        dijkstra_stack_shortest_path start state
          ∧ ¬ head = goal
          ∧ state.stack = head :: tail
        → dijkstra_stack_shortest_path start (hsearch_step_expand h_zero state head tail) := by
    intro head tail ⟨prior_invar,head_is_not_goal,compose⟩
    unfold dijkstra_stack_shortest_path --at prior_invar ⊢
    intro v v_visited_after not_on_stack_or_head

    simp at compose v_visited_after not_on_stack_or_head prior_invar ⊢



    -- properties of the current head
    have head_was_visited_before : head ∈ state.visited := by simp_all
    -- there is a path to head and it is as long as we memorised:w

    let path_to_head : g.Path start head :=
      (extract_path_to start head state head_was_visited_before mother_invar mother_invar_adj decreasing_invar).1

    -- cost of path_to_head is what we memorised
    have ph_eq_dh : path_to_head.cost = (state.pathOrder head).1 := by
      unfold dijkstra_stack_shortest_path at prior_invar
      apply eq_of_le_of_ge
      · apply hsearch_path_extracted_not_longer_than_path_order
        exact path_order_diff
      · specialize prior_invar head head_was_visited_before
        simp_all
        unfold cost_is at prior_invar
        obtain ⟨hp, ⟨ hp_cost, hp_cheapest ⟩ ⟩ := prior_invar
        unfold Path.is_cheapest at hp_cheapest
        specialize hp_cheapest path_to_head
        rw [hp_cost] at hp_cheapest
        simp_all

    have support_visited : ∀ u ∈ path_to_head.val.support, u ∈ state.visited := by
      apply support_of_path_visited
      unfold path_to_head
      rfl



    by_cases v_not_start : v ≠ start
    · cases not_on_stack_or_head
      · next v_not_on_stack =>
        specialize prior_invar v
        unfold hsearch_step_expand at v_not_on_stack v_visited_after ⊢
        simp at v_visited_after
        cases v_visited_after
        · next v_was_visited =>
          simp_all
          have invar_taut : ¬v = head ∨ head = v := by grind
          specialize prior_invar invar_taut
          grind
        · next both =>
          obtain ⟨ head_adj_v, v_was_not_visited ⟩ := both
          simp_all -- contractiction. This case is impossible
      · next v_now_stack_head =>
        simp at v_now_stack_head
        obtain ⟨ stack_not_empty_after, head_after_is_v ⟩ := v_now_stack_head
        unfold cost_is


        by_cases v_visited : v ∈ state.visited
        ·
          -- v is *now* the head of the stack, but it was already visited before.
          -- this means it had to already have been on the stack before
          have mother_options := hsearch_mother_options h_zero state head tail ⟨v,v_visited⟩ v_visited_after
          cases mother_options
          case pos.inl mother_is_head =>
            have adj_head_v : g.Adj head v := by
              unfold hsearch_step_expand at mother_is_head
              unfold search_invar_mother_is_adjacent at mother_invar_adj
              specialize mother_invar_adj ⟨ v, v_visited ⟩ v_not_start
              grind

            have v_ne_head : v ≠ head := by
              by_contra v_eq_head
              subst v_eq_head
              unfold hsearch_step_expand at mother_is_head
              unfold search_invar_mother_decreasing_path_order at decreasing_invar
              specialize decreasing_invar ⟨ v, v_visited ⟩ v_not_start
              simp_all
              apply FValueComp.lt_irr (state.pathOrder v) decreasing_invar

            let e := edgeCost adj_head_v
            have v_order_eq_head_plus_edge : ((hsearch_step_expand h_zero state head tail).pathOrder v).1 = ((hsearch_step_expand h_zero state head tail).pathOrder head).1 + e := by
              unfold hsearch_step_expand at mother_is_head ⊢
              simp_all
              grind

            have v_not_mem_ph_support : v ∉ ↑path_to_head.val.support := by
              by_contra v_in_support
              have h := (extract_path_to start head state head_was_visited_before mother_invar mother_invar_adj decreasing_invar).2
              specialize h v (by apply v_in_support) v_ne_head
              unfold hsearch_step_expand at v_order_eq_head_plus_edge mother_is_head
              simp_all
              have v_visited : v ∈ state.visited := by grind
              unfold search_invar_mother_decreasing_path_order at decreasing_invar
              specialize decreasing_invar ⟨ v, v_visited ⟩ v_not_start
              split_ifs at v_order_eq_head_plus_edge <;> (try  grind)
              · simp_all
                have order_eq := FValueComp.lt_antisymm (state.pathOrder head) (state.pathOrder v) decreasing_invar h
                rw [order_eq] at h
                apply FValueComp.lt_irr (state.pathOrder v) h
              · simp_all
                have order_eq := FValueComp.lt_antisymm (state.pathOrder head) (state.pathOrder v) decreasing_invar h
                rw [order_eq] at h
                apply FValueComp.lt_irr (state.pathOrder v) h
              · simp_all
                have order_eq := FValueComp.lt_antisymm (state.pathOrder head) (state.pathOrder v) decreasing_invar h
                rw [order_eq] at h
                apply FValueComp.lt_irr (state.pathOrder v) h
              all_goals
                rename_i a b c
                unfold edgeCost at c v_order_eq_head_plus_edge
                unfold FValueComp.lt Nat.instFValueCompProd at h
                simp_all
                apply Prod.lex_iff.mp at h
                cases h
                · grind
                next prop =>
                  obtain ⟨ eq, lt ⟩ := prop
                  have e_zero : e = 0 := by omega
                  simp_all
                  have o_eq : state.pathOrder v = ((state.pathOrder head).1, (state.pathOrder head).2 + 1) := by grind
                  specialize mother_is_head o_eq
                  grind

            let path_to_v : g.Path start v := path_to_head.concat adj_head_v v_not_mem_ph_support

            use path_to_v
            constructor
            · unfold path_to_v
              rw [WeightedDiGraph.Path.concat_inc_cost_by_edge]
              unfold hsearch_step_expand
              simp_all
              unfold edgeCost
              rw [add_comm]
              split_ifs <;> try grind
              rename_i v_lt_head_edge
              unfold hsearch_step_expand at v_order_eq_head_plus_edge
              simp_all
              unfold e edgeCost at v_order_eq_head_plus_edge
              split_ifs at v_order_eq_head_plus_edge <;> grind
            · apply dijkstra_path_head_adj_new_head_is_cheapest <;> try assumption
              · intro p_start_v ⟨p_lt_ph_e,v_visited,cond3⟩
                obtain ⟨ w,path_start_w,w_adj_v,v_not_earlier_in_path,p_start_v_compose⟩ := p_start_v.split_at_end (Ne.symm v_not_start)

                have w_ne_v : w ≠ v := by
                  by_contra w_eq_v
                  rw [← w_eq_v] at v_not_earlier_in_path
                  have w_in_supp : w ∈ path_start_w.val.support := Path.goal_in_support path_start_w
                  contradiction


                have p_start_v_cost : p_start_v.val.cost = edgeCost w_adj_v + path_start_w.val.cost := by
                  rw [p_start_v_compose] ; simp

                have w_in_supp : w ∈ p_start_v.val.support := by rw [p_start_v_compose] ; simp
                have w_visited : w ∈ state.visited := by specialize cond3 w w_in_supp w_ne_v ; exact cond3.right
                have w_ne_mem_stack : w ∉ state.stack := by specialize cond3 w w_in_supp w_ne_v ; exact cond3.left

                have w_order_eq : (state.pathOrder w).1 ≤ path_start_w.val.cost := by
                  unfold dijkstra_stack_shortest_path at prior_invar
                  specialize prior_invar w w_visited
                  simp_all
                  unfold cost_is at prior_invar
                  obtain ⟨sp, ⟨ cost_eq_order, cheapest⟩ ⟩ := prior_invar
                  unfold Path.is_cheapest at cheapest
                  specialize cheapest path_start_w
                  rw [cost_eq_order] at cheapest
                  apply cheapest

                have v_updated_from_w : (state.pathOrder v).1 ≤ (state.pathOrder w).1 + edgeCost w_adj_v := by
                  unfold hsearch_invar_on_stack_or_all_neighbours_max_order at update_invar
                  specialize update_invar ⟨ w, w_visited ⟩  w_ne_mem_stack v w_adj_v
                  exact update_invar

                conv at p_lt_ph_e => left ; unfold Path.cost


                have t_1 : (state.pathOrder v).1 ≤ path_start_w.val.cost + edgeCost w_adj_v := by omega
                have t_2 : (state.pathOrder v).1 ≤ p_start_v.val.cost := by omega
                have t_3 : (state.pathOrder v).1 < (path_to_head.concat adj_head_v v_not_mem_ph_support).cost := by omega
                unfold Path.concat at t_3
                simp at t_3
                unfold Path.cost at ph_eq_dh
                rw [ph_eq_dh] at t_3
                unfold hsearch_step_expand at v_order_eq_head_plus_edge
                simp_all
                split_ifs at v_order_eq_head_plus_edge <;> omega
          · obtain ⟨mother_same, mother_ne_head⟩ := ‹_›
            let the_mother := state.mother ⟨v, v_visited⟩
            have mother_visited : the_mother ∈ state.visited := by
              unfold search_invar_mother_is_visited at mother_invar
              specialize mother_invar ⟨ v, v_visited ⟩
              grind
            have pathOrder_unchanged : (hsearch_step_expand h_zero state head tail).pathOrder v = state.pathOrder v := by
              unfold hsearch_step_expand at mother_same ⊢
              grind
            have adj_mother_v : g.Adj the_mother v := by
              unfold search_invar_mother_is_adjacent at mother_invar_adj
              specialize mother_invar_adj ⟨ v, v_visited ⟩
              grind

            have mother_and_edge_smaller_order_before : (state.pathOrder the_mother).1 + edgeCost adj_mother_v ≤ (state.pathOrder v).1 := by
              unfold hsearch_path_order_diff_by_edge_cost at path_order_diff
              specialize path_order_diff mother_invar_adj v v_visited v_not_start
              unfold the_mother
              grind

            have pathOrder_mother_decreases : ((hsearch_step_expand h_zero state head tail).pathOrder the_mother).1 ≤ (state.pathOrder the_mother).1 := by
              unfold hsearch_step_expand
              simp_all
              grind


            have mother_not_on_stack : the_mother ∉ state.stack := by
              unfold hsearch_step_expand at mother_same
              simp_all
              constructor
              · grind
              · by_contra mother_in_tail
                have mother_neq_v : the_mother ≠ v := by
                  intro h
                  specialize decreasing_invar ⟨v, v_visited⟩ (by simp_all)
                  simp at decreasing_invar
                  nth_rewrite 2 [← h] at decreasing_invar
                  exact FValueComp.lt_irr _ decreasing_invar
                have mother_now_geq :((hsearch_step_expand h_zero state head tail).pathOrder the_mother).1 ≥ ((hsearch_step_expand h_zero state head tail).pathOrder v).1 := by
                  unfold hsearch_step_expand at head_after_is_v
                  simp_all
                  apply mergeSort_head_from_head_unsorted at head_after_is_v
                  · specialize head_after_is_v the_mother (by simp; left ; exact mother_in_tail)
                    cases head_after_is_v
                    case inl mother_v => contradiction
                    case inr h =>
                      unfold hsearch_step_expand
                      simp_all
                      split_ifs
                      all_goals
                        simp_all
                        split_ifs at h
                        all_goals
                          cases h
                          · grind
                          · rename_i r
                            unfold Nat.instFValueCompProd at r
                            simp at r
                            grind
                  · intros; apply hsearch_merge_trans <;> assumption
                  · intros; apply hsearch_merge_total

                have mother_now_geq_v_bef :((hsearch_step_expand h_zero state head tail).pathOrder the_mother).1 ≥ (state.pathOrder v).1 := by grind

                by_cases zero_cost_edge : edgeCost adj_mother_v = 0
                ·
                  have mother_le_order_before : (state.pathOrder the_mother).1 ≤ (state.pathOrder v).1 := by omega
                  have mother_ge_order_before : (state.pathOrder the_mother).1 ≥ (state.pathOrder v).1 := by omega
                  have mother_eq_order_before : (state.pathOrder the_mother).1 = (state.pathOrder v).1 := by omega

                  clear mother_le_order_before mother_ge_order_before
                  unfold hsearch_step_expand at head_after_is_v
                  simp_all
                  apply mergeSort_head_from_head_unsorted at head_after_is_v
                  · specialize head_after_is_v the_mother (by simp; left ; exact mother_in_tail)
                    cases head_after_is_v
                    case pos.inl mother_v => contradiction
                    case pos.inr h =>

                      unfold search_invar_mother_decreasing_path_order at decreasing_invar
                      specialize decreasing_invar ⟨ v , v_visited ⟩ v_not_start
                      unfold FValueComp.lt Nat.instFValueCompProd at decreasing_invar
                      simp at decreasing_invar
                      apply Prod.lex_iff.mp at decreasing_invar
                      have p' : (state.pathOrder (state.mother ⟨v, v_visited⟩)).2 < (state.pathOrder v).2 := by grind

                      simp_all
                      split_ifs at h
                      rotate_left 9
                      · simp_all
                        cases h
                        · try simp_all
                          grind
                        · rename_i r
                          unfold Nat.instFValueCompProd at r
                          simp at r
                          apply Prod.lex_iff.mp at r
                          have p : (state.pathOrder v).2 < (state.pathOrder the_mother).2 := by
                            cases r
                            case inl h =>
                              simp_all
                              rename_i a b c
                              unfold edgeCost at a b c h mother_eq_order_before decreasing_invar
                              have adj_head_v : g.Adj head v := by grind
                              have adj_head_mother : g.Adj head the_mother := by grind

                              by_cases edgeCost adj_head_v = edgeCost adj_head_mother
                              · rename_i cost_eq
                                specialize b (by unfold edgeCost at cost_eq ; grind)
                                unfold hsearch_step_expand at pathOrder_unchanged
                                simp at pathOrder_unchanged
                                unfold edgeCost at pathOrder_unchanged
                                specialize pathOrder_unchanged adj_head_v
                                simp [*] at pathOrder_unchanged
                                have h : (state.pathOrder head).2 + 1 = (state.pathOrder v).2 := by grind
                                grind
                              · have v_lt_m : edgeCost adj_head_v < edgeCost adj_head_mother := by
                                  rename_i neq
                                  unfold edgeCost at neq ⊢
                                  grind
                                unfold hsearch_step_expand at pathOrder_unchanged
                                simp at pathOrder_unchanged
                                unfold edgeCost at pathOrder_unchanged
                                specialize pathOrder_unchanged adj_head_v
                                simp [*] at pathOrder_unchanged
                                specialize pathOrder_unchanged (by grind)
                                have h : (state.pathOrder head).2 + 1 = (state.pathOrder v).2 := by grind
                                grind
                            · grind
                          clear r
                          unfold the_mother at p
                          omega
                      all_goals
                        simp_all
                        cases h
                        · simp_all
                          try grind
                        · rename_i r
                          unfold Nat.instFValueCompProd at r
                          simp at r
                          apply Prod.lex_iff.mp at r
                          have p : (state.pathOrder v).2 < (state.pathOrder the_mother).2 := by grind
                          clear r
                          unfold the_mother at p
                          omega
                  · intros; apply hsearch_merge_trans <;> assumption
                  · intros; apply hsearch_merge_total

                · have mother_smaller_order_before : (state.pathOrder the_mother).1 < (state.pathOrder v).1 := by omega
                  have mother_now_smaller_order_before : ((hsearch_step_expand h_zero state head tail).pathOrder the_mother).1 < ((hsearch_step_expand h_zero state head tail).pathOrder v).1 := by grind
                  have mother_now_geq :((hsearch_step_expand h_zero state head tail).pathOrder the_mother).1 ≥ ((hsearch_step_expand h_zero state head tail).pathOrder v).1 := by
                    unfold hsearch_step_expand at head_after_is_v
                    simp_all
                  omega

            -- path to v is the path it was before. This will be a path to its mother and then that edge
            let path_mother := (extract_path_to start the_mother state mother_visited mother_invar mother_invar_adj decreasing_invar).1


            have v_not_in_mother_path : v ∉ path_mother.val.support := by
              intro v_in_path_mother
              have path_order := (extract_path_to start the_mother state mother_visited
                mother_invar mother_invar_adj decreasing_invar).2
              -- v ≠ the_mother (since pathOrderstart_not_mem_tail the_mother ≺ pathOrder v, so they differ)
              have v_ne_mother : v ≠ the_mother := by
                intro h--; subst h
                have decr := decreasing_invar ⟨v, v_visited⟩ v_not_start
                simp at decr
                nth_rewrite 2 [h] at decr
                exact FValueComp.lt_irr _ decr
              -- extract_path_to .2: pathOrder v ≺ pathOrder the_mother
              have pv_lt_pm := path_order v v_in_path_mother v_ne_mother
              -- decreasing_invar: pathOrder the_mother ≺ pathOrder v
              have pm_lt_pv := decreasing_invar ⟨v, v_visited⟩ v_not_start
              -- cycle: pathOrder v ≺ pathOrder the_mother ≺ pathOrder v
              exact FValueComp.lt_irr _ (FValueComp.lt_trans _ _ _ pv_lt_pm pm_lt_pv)
            let path_mother_v := path_mother.concat adj_mother_v v_not_in_mother_path

            use path_mother_v
            constructor
            · rw [pathOrder_unchanged]
              unfold path_mother_v
              rw [Path.concat_inc_cost_by_edge]
              apply eq_of_le_of_ge
              · have original_path_order_diff := path_order_diff
                unfold hsearch_path_order_diff_by_edge_cost at path_order_diff
                specialize path_order_diff mother_invar_adj v v_visited v_not_start
                apply le_trans ; rotate_left
                · apply path_order_diff
                · nth_rewrite 1 [add_comm]
                  apply add_le_add_left
                  unfold path_mother
                  apply hsearch_path_extracted_not_longer_than_path_order
                  exact original_path_order_diff
              · unfold hsearch_invar_on_stack_or_all_neighbours_max_order at update_invar
                specialize update_invar ⟨ the_mother, mother_visited ⟩ mother_not_on_stack v adj_mother_v
                rw [add_comm]
                apply le_trans
                · apply update_invar
                · apply add_le_add_left
                  unfold dijkstra_stack_shortest_path at prior_invar
                  specialize prior_invar the_mother
                  simp_all
                  unfold cost_is at prior_invar
                  obtain ⟨ p, p_cost, is_cheapest ⟩ := prior_invar
                  unfold Path.is_cheapest at is_cheapest
                  specialize is_cheapest path_mother
                  unfold Path.cost at is_cheapest p_cost
                  convert is_cheapest
                  exact p_cost.symm
            · rename_i h
              obtain ⟨ mother_remains, mother_ne_head ⟩ := h
              unfold Path.is_cheapest
              intro p'
              by_contra p'_cheaper; simp at p'_cheaper
              have pm_eq_dm : path_mother.val.cost = (state.pathOrder the_mother).1 := by
                apply eq_of_le_of_ge
                · apply hsearch_path_extracted_not_longer_than_path_order
                  assumption
                · specialize prior_invar the_mother mother_visited
                  simp [mother_not_on_stack] at prior_invar
                  unfold cost_is at prior_invar
                  obtain ⟨opti_p, opti_cost, is_cheapest ⟩ := prior_invar
                  unfold Path.is_cheapest at is_cheapest
                  specialize is_cheapest path_mother
                  rw [opti_cost] at is_cheapest
                  unfold Path.cost at is_cheapest
                  omega

              apply dijkstra_path_mother_adj_new_head_is_cheapest (start:=start) (v:=v) (p':=p') (path_mother:=path_mother) <;> try assumption
              · rfl
              · unfold path_mother ; rfl
              · intro p_start_v ⟨p_lt_ph_e,v_visited,cond3⟩
                obtain ⟨ w,path_start_w,w_adj_v,v_not_earlier_in_path,p_start_v_compose⟩ := p_start_v.split_at_end (Ne.symm v_not_start)

                have w_ne_v : w ≠ v := by
                  by_contra w_eq_v
                  rw [← w_eq_v] at v_not_earlier_in_path
                  have w_in_supp : w ∈ path_start_w.val.support := Path.goal_in_support path_start_w
                  contradiction


                have p_start_v_cost : p_start_v.val.cost = edgeCost w_adj_v + path_start_w.val.cost := by
                  rw [p_start_v_compose] ; simp

                have w_in_supp : w ∈ p_start_v.val.support := by rw [p_start_v_compose] ; simp
                have w_visited : w ∈ state.visited := by specialize cond3 w w_in_supp w_ne_v ; exact cond3.right
                have w_ne_mem_stack : w ∉ state.stack := by specialize cond3 w w_in_supp w_ne_v ; exact cond3.left

                have w_order_eq : (state.pathOrder w).1 ≤ path_start_w.val.cost := by
                  unfold dijkstra_stack_shortest_path at prior_invar
                  specialize prior_invar w w_visited
                  simp_all
                  unfold cost_is at prior_invar
                  obtain ⟨sp, ⟨ cost_eq_order, cheapest⟩ ⟩ := prior_invar
                  unfold Path.is_cheapest at cheapest
                  specialize cheapest path_start_w
                  rw [cost_eq_order] at cheapest
                  apply cheapest

                have v_updated_from_w : (state.pathOrder v).1 ≤ (state.pathOrder w).1 + edgeCost w_adj_v := by
                  unfold hsearch_invar_on_stack_or_all_neighbours_max_order at update_invar
                  specialize update_invar ⟨ w, w_visited ⟩  w_ne_mem_stack v w_adj_v
                  exact update_invar

                conv at p_lt_ph_e => left ; unfold Path.cost


                have t_1 : (state.pathOrder v).1 ≤ path_start_w.val.cost + edgeCost w_adj_v := by omega
                have t_2 : (state.pathOrder v).1 ≤ p_start_v.val.cost := by omega
                have t_3 : (state.pathOrder v).1 < (path_mother.concat adj_mother_v v_not_in_mother_path).cost := by omega
                unfold Path.concat at t_3
                simp at t_3
                unfold Path.cost at ph_eq_dh
                rw [pm_eq_dm] at t_3
                omega
        · unfold hsearch_step_expand at v_visited_after
          simp at v_visited_after
          simp [v_visited] at v_visited_after

          let e := edgeCost v_visited_after
          have v_order_eq_head_plus_edge : ((hsearch_step_expand h_zero state head tail).pathOrder v).1 = ((hsearch_step_expand h_zero state head tail).pathOrder head).1 + e := by
            unfold hsearch_step_expand
            simp_all
            grind

          let path_to_v : g.Path start v := path_to_head.concat v_visited_after (by
            by_contra v_in_support
            have v_visited_before := support_visited v v_in_support
            contradiction)


          use path_to_v
          constructor
          · unfold path_to_v
            rw [WeightedDiGraph.Path.concat_inc_cost_by_edge]
            unfold hsearch_step_expand
            simp_all
            unfold edgeCost
            rw [add_comm]
          · -- Situation: v is head of stack after expansion of head
            -- v was added to the stack due to expansion of v (i.e. it was not visited before)
            -- ph (path_to_head) is a shortest path to head
            -- selected apth to v is (path_to_head ; <head,v>)
            --
            -- Now: Assume there is a shorter path to v: p'
            apply dijkstra_path_head_adj_new_head_is_cheapest <;> try assumption
            · grind
            --· grind
    · simp at v_not_start
      subst v_not_start
      apply dijkstra_expand_keeps_shortest_path_invar_start
      · exact start_visited
      · exact start_path_order
      · apply head_is_not_goal
      · exact compose

lemma dijkstra_expand_keeps_stack_sorted(goal : V) :
    ∀ head : V, ∀ tail : List V,
      dijkstra_stack_sorted state
        ∧ head ≠ goal
        ∧ state.stack = head :: tail
      → dijkstra_stack_sorted  (hsearch_step_expand h_zero state head tail) := by
  intro head tail ⟨ prior_invar,head_ne_goal,compose⟩
  unfold dijkstra_stack_sorted
  unfold hsearch_step_expand
  apply merge_two_prop
  · intro a b c a_b b_c
    apply hsearch_merge_trans
    · apply a_b
    · apply b_c
  · intro a b
    apply hsearch_merge_total
  · ext x y
    simp

end

lemma dijkstra_expand_carries_all_dijkstra_invars (start : V) (goal : V):
      WeightedDiGraph.base_invar_carries_over_expand (hsearch_step_expand (g:=g) h_zero) goal (dijkstra_all_invar (g:=g)  start) := by
      unfold WeightedDiGraph.base_invar_carries_over_expand
      intro s head tail ⟨ invar_before, head_ne_goal, compose⟩
      unfold dijkstra_all_invar
      constructor
      · apply hsearch_expand_keeps_base_invars
        · exact ⟨ invar_before.left, head_ne_goal, compose⟩
      · and_intros
        · apply dijkstra_expand_keeps_shortest_path_invar
          · exact invar_before.left.right.left
          · exact invar_before.left.right.right.left
          · exact invar_before.left.right.right.right.left
          · exact invar_before.left.right.right.right.right.right
          · exact invar_before.left.right.right.right.right.left
          · exact invar_before.left.left
          · exact invar_before.right.right.left
          · exact invar_before.right.right.right.left
          --· exact invar_before.right.right.right.right.left
          · exact invar_before.right.right.right.right.right.left
          · exact invar_before.right.right.right.right.right.right.left
          · exact invar_before.right.right.right.right.right.right.right
          · exact ⟨ invar_before.right.left, head_ne_goal, compose⟩
        · apply hsearch_expand_keeps_on_path_order_diff
          · exact invar_before.left.left
          · exact invar_before.left.right.right.left
          · exact invar_before.left.right.left
          · exact ⟨ invar_before.right.right.left, head_ne_goal, compose⟩
        · apply hsearch_expand_keeps_on_stack_or_nei_max_order
          · exact invar_before.left.right.right.right.right.left
          · exact ⟨ invar_before.right.right.right.left, head_ne_goal, compose⟩
        · apply dijkstra_expand_keeps_stack_sorted
          · exact ⟨ invar_before.right.right.right.right.left, head_ne_goal, compose⟩
        · apply hsearch_expand_start_path_order_zero_carries
          · exact invar_before.left.right.right.right.right.right
          · exact ⟨ invar_before.right.right.right.right.right.left, head_ne_goal, compose⟩
        · apply dijkstra_expand_start_not_mem_tail_carries
          · exact invar_before.left.right.right.right.right.right
          · exact invar_before.right.right.right.right.right.left
          · exact ⟨ invar_before.right.right.right.right.right.right.left, head_ne_goal, compose⟩
        · apply dijkstra_expand_stack_nodup_carries
          · exact invar_before.left.left
          · exact ⟨ invar_before.right.right.right.right.right.right.right, head_ne_goal, compose⟩

theorem dijkstra_is_optimal (start : V) (goal : V)
    (returned_path : Option.isSome (dijkstra (g:=g) start goal)):
    ((dijkstra (g:=g) start goal).get returned_path).is_cheapest := by
    let final : WeightedDiGraph.base_search_state g (ℕ×ℕ) × Bool := WeightedDiGraph.search_with_stack_step (goal:=goal) (start_state := WeightedDiGraph.base_search_state_initial start (0,0)) (hsearch_step_expand h_zero) (hsearch_expand_metric_reduction h_zero)
    let final_state := final.1
    -- general properties
    have h_4 : WeightedDiGraph.search_prop_stack_head_is_goal goal final_state := by
      unfold final_state
      unfold final
      unfold WeightedDiGraph.search_with_stack_step
      simp
      unfold WeightedDiGraph.search_internal
      apply WeightedDiGraph.search_recurse_obtain_base_termination_property (G:=g) (D:=ℕ×ℕ) (T:=(Vector (WithTop (ℕ × ℕ)) g.nodeNum) × ℕ) goal (WeightedDiGraph.base_search_state_initial start (0,0)) (property_after_termination := WeightedDiGraph.search_prop_stack_head_is_goal (D:=ℕ×ℕ) goal ) (terminated_with := true) (search_step := WeightedDiGraph.search_stack_step (G:=g) (D:=ℕ×ℕ) (hsearch_step_expand (g:=g) h_zero)) (hsearch_termination_metric)
      · intro s
        apply WeightedDiGraph.search_stack_step_goal_stack_head_if_terminated
      · unfold dijkstra at returned_path
        unfold WeightedDiGraph.search_exe_with_stack_step at returned_path
        unfold WeightedDiGraph.search_exe at returned_path
        simp_all
        apply returned_path

    have t_0 : WeightedDiGraph.search_invar_stack_is_visited final_state := by
      unfold final_state
      unfold final
      unfold WeightedDiGraph.search_with_stack_step
      simp only []
      apply WeightedDiGraph.search_returns_with_stack_visited (state_type := WeightedDiGraph.base_search_state g (ℕ×ℕ)) (start_state := WeightedDiGraph.base_search_state_initial start (0,0)) (start := start)
      · rfl
      · apply WeightedDiGraph.base_invar_carries_over_stack_step
        apply hsearch_expand_keeps_base_invars

    have h_3 : WeightedDiGraph.search_prop_goal_visited goal final_state := by
      apply t_0
      unfold WeightedDiGraph.search_prop_stack_head_is_goal at h_4
      apply List.eq_cons_of_mem_head? at h_4
      rw [h_4]
      simp

    have t_1 : WeightedDiGraph.search_invar_mother_is_visited final_state := by
      unfold final_state
      unfold final
      unfold WeightedDiGraph.search_with_stack_step
      simp only []
      apply WeightedDiGraph.search_returns_with_mother_visited (state_type := WeightedDiGraph.base_search_state g (ℕ×ℕ)) (start_state := WeightedDiGraph.base_search_state_initial start (0,0)) (start := start)
      · rfl
      · apply WeightedDiGraph.base_invar_carries_over_stack_step
        apply hsearch_expand_keeps_base_invars

    have t_2 : WeightedDiGraph.search_invar_mother_is_adjacent start final_state := by
      unfold final_state
      unfold final
      unfold WeightedDiGraph.search_with_stack_step
      simp only []
      apply WeightedDiGraph.search_returns_with_mother_adjacent (state_type := WeightedDiGraph.base_search_state g (ℕ×ℕ)) (start_state := WeightedDiGraph.base_search_state_initial start (0,0)) (start := start)
      · rfl
      · apply WeightedDiGraph.base_invar_carries_over_stack_step
        apply hsearch_expand_keeps_base_invars

    have t_3 : WeightedDiGraph.search_invar_mother_decreasing_path_order start final_state := by
      unfold final_state
      unfold final
      unfold WeightedDiGraph.search_with_stack_step
      simp only []
      apply WeightedDiGraph.search_returns_with_mother_decreasing (state_type := WeightedDiGraph.base_search_state g (ℕ×ℕ)) (start_state := WeightedDiGraph.base_search_state_initial start (0,0)) (start := start)
      · rfl
      · apply WeightedDiGraph.base_invar_carries_over_stack_step
        apply hsearch_expand_keeps_base_invars

    -- Dijkstra specific ones
    have dijkstra_full_invar_at_end : dijkstra_all_invar start final_state := by
     have right_class : (fun s => dijkstra_all_invar start (WeightedDiGraph.has_base_search_state.to_base_state (G:=g) s)) final_state := by
      unfold final_state
      unfold final
      unfold WeightedDiGraph.search_with_stack_step
      unfold WeightedDiGraph.search_internal
      simp
      apply WeightedDiGraph.search_recurse_lift_base_invariant
      constructor
      · apply dijkstra_invar_holds_at_init
      · apply WeightedDiGraph.base_invar_carries_over_stack_step
        apply dijkstra_expand_carries_all_dijkstra_invars
     -- needs to be applied, lean4 has problems with they type-class here
     apply right_class

    have i_1 : dijkstra_stack_shortest_path start final_state := dijkstra_full_invar_at_end.2.1

    have h : g.cost_is start goal (final_state.pathOrder goal).1 := by
     have i_1' := i_1 goal h_3
     unfold WeightedDiGraph.search_prop_stack_head_is_goal at h_4
     apply i_1'
     right
     obtain ⟨ tail, compose ⟩ := List.head?_eq_some_iff.mp h_4
     simp_all

    unfold dijkstra WeightedDiGraph.search_exe_with_stack_step
    unfold WeightedDiGraph.search_exe WeightedDiGraph.Path.is_cheapest
    intro p'
    unfold WeightedDiGraph.distance_is at h
    obtain ⟨p, ⟨ p_path_length, p_is_cheapest ⟩ ⟩  := h

    have prop := hsearch_path_extracted_not_longer_than_path_order start final_state t_1 t_2 t_3 dijkstra_full_invar_at_end.2.2.1
    unfold final_state at prop
    unfold final at prop
    unfold WeightedDiGraph.search_with_stack_step at prop
    simp_all
    unfold WeightedDiGraph.has_base_search_state.to_base_state
    unfold WeightedDiGraph.instHas_base_search_stateBase_search_state
    apply le_trans
    · apply prop
    · clear prop t_1 t_2 t_3
      unfold final_state at p_path_length
      unfold final at p_path_length
      unfold WeightedDiGraph.search_with_stack_step at p_path_length
      simp_all
      rw [← p_path_length]
      unfold WeightedDiGraph.Path.is_cheapest at p_is_cheapest
      specialize p_is_cheapest p'
      simp_all


end NatGraph
