import Graphlib.HeuristicSearch

-- def local global variable for a graph
variable {V : Type} [FinEnum V]
variable {g : NatGraph V}

namespace NatGraph

open WeightedDiGraph

/-- a heuristic is admissible iff for all nodes, the true cost is greater or equal to the heuristic --/
abbrev admissible (heur : V → ℕ) (goal : V) :=
  ∀ v : V, g.cost_ge v goal (heur v)

abbrev admissible' (heur : V → ℕ) (goals : List V) :=
  ∀ v : V, ∀ goal ∈ goals, g.cost_ge v goal (heur v)

abbrev goal_aware (heur : V → ℕ) (goal : V) := heur goal = 0

abbrev goal_aware' (heur : V → ℕ) (goals : List V) := ∀ goal ∈ goals, heur goal = 0

abbrev consistent (heur : V → ℕ) :=
  ∀ v : V, ∀ w : V, ∀ adj : g.Adj v w, (heur v) ≤ (heur w) + g.edgeCost adj

private lemma walk_cost_ge_heur (heur : V → ℕ) (goal : V)
    (ga : goal_aware heur goal) (hcons : consistent (g:=g) heur)
    {v : V} (w : g.Walk v goal) : w.cost ≥ heur v := by
  induction w with
  | nil => simp [Walk.cost, ga]
  | cons adj rest ih =>
    have ih' := ih ga
    calc heur _ ≤ heur _ + g.edgeCost adj := hcons _ _ adj
      _ ≤ rest.cost + g.edgeCost adj := Nat.add_le_add_right ih' _
      _ = g.edgeCost adj + rest.cost := Nat.add_comm _ _
lemma admissible_of_goal_aware_consistent (heur : V → ℕ) (goal : V) :
    goal_aware heur goal ∧ consistent (g:=g) heur → admissible (g:=g) heur goal := by
  intro ⟨ga, cons⟩ v p
  exact walk_cost_ge_heur heur goal ga cons p.val

lemma admissible'_of_goal_aware_consistent (heur : V → ℕ) (goals : List V) :
    goal_aware' heur goals ∧ consistent (g:=g) heur → admissible' (g:=g) heur goals := by
  intro ⟨ga, cons⟩ v goal goal_in_goals p
  exact walk_cost_ge_heur heur goal (ga goal goal_in_goals) cons p.val

variable (heur : V → ℕ)

/-- The A* algorithm, defined via `WeightedDiGraph.search_exe_with_stack_step`. -/
def astar (start : V) (goal : V): Option (g.Path start goal) :=
  let start_state := WeightedDiGraph.base_search_state_initial start ⟨0,0⟩
  have h : WeightedDiGraph.has_base_search_state.to_base_state (G:=g) start_state = WeightedDiGraph.base_search_state_initial start (0,0):= by simp_all only [start_state]; rfl

  WeightedDiGraph.search_exe_with_stack_step (G:=g) (start := start) (goal:=goal) (start_state:=start_state) (termination_metric := hsearch_termination_metric) (hsearch_step_expand heur) (hsearch_expand_metric_reduction heur) (hsearch_expand_keeps_base_invars heur) h

def astar_last_state (start : V) (goal : V): WeightedDiGraph.base_search_state g (ℕ×ℕ) × Bool :=
  WeightedDiGraph.search_with_stack_step (goal:=goal) (start_state := WeightedDiGraph.base_search_state_initial start (0,0)) (hsearch_step_expand heur) (hsearch_expand_metric_reduction heur)

theorem astar_is_sound (start : V) (goal : V) :
    (Option.isSome (astar (g:=g) heur start goal) → (∃ x : (g.Path start goal), x = x)) := by
  apply WeightedDiGraph.search_with_stack_step_is_sound
  · apply hsearch_expand_metric_reduction
  · apply hsearch_expand_keeps_base_invars
  · rfl

theorem astar_is_complete (start : V) (goal : V):
    ((∃ x : (g.Path start goal), x = x) → Option.isSome (astar (g:=g) heur start goal)) := by
  apply WeightedDiGraph.search_with_stack_step_is_complete
  · apply hsearch_expand_metric_reduction
  · apply hsearch_expand_keeps_base_invars
  · rfl
  · apply hsearch_expand_keeps_goal_on_stack
  · apply hsearch_expand_goal_becomes_visited_puts_it_on_stack

/-! ## Optimality proof --/

/- The stack is sorted by the path_order (i.e. distance) value. -/
abbrev astar_stack_sorted (s : WeightedDiGraph.base_search_state g (ℕ×ℕ)) :=
  List.Pairwise (fun u v =>
    (add_heur u (s.pathOrder u) heur = add_heur v (s.pathOrder v) heur) ∨ (add_heur u (s.pathOrder u) heur ≺ add_heur v (s.pathOrder v) heur)) s.stack

abbrev node_open (s : WeightedDiGraph.base_search_state g (ℕ×ℕ)) (v : V) :=
  v ∈ s.stack

abbrev node_closed (s : WeightedDiGraph.base_search_state g (ℕ×ℕ)) (v : V) :=
  v ∈ s.visited ∧ v ∉ s.stack

/-- Invariant propose by Hart et al, 1968 (lemma 1):
    any non-closed node v (i.e. any node that is either on the stack or not visited)
    for all optimal paths p from start to it
    there is an open node v' on p for which its current known distance from start is the optimum. -/
abbrev astar_invar (start : V) (s : WeightedDiGraph.base_search_state g (ℕ×ℕ)) :=
  ∀ v : V, ¬ (node_closed s v) → ∀ p : g.Path start v, p.is_cheapest →
    ∃ v' ∈ p.support, (node_open s v') ∧ g.cost_is start v' (s.pathOrder v').1

abbrev astar_path_invar (start : V) (goal : V) (s : WeightedDiGraph.base_search_state g (ℕ×ℕ)) :=
  --∀ p : g.Path start goal, p.is_cheapest → ∃ v' ∈ p.support, (node_open s v')
  ∀ p : g.Path start goal, ∃ v' ∈ p.support, (node_open s v')

abbrev astar_goal_invar (goal : V) (s : WeightedDiGraph.base_search_state g (ℕ×ℕ)) :=
  goal ∈ s.visited → goal ∈ s.stack


lemma astar_invar_holds_at_init (start : V):
  astar_invar start (WeightedDiGraph.base_search_state_initial (G:=g) start (0,0)) := by
  unfold astar_invar
  unfold WeightedDiGraph.base_search_state_initial
  simp_all
  intro v a nodup cheapest
  use start
  constructor
  · simp
  · unfold node_open
    simp
    apply cost_v_v


lemma walk_more_costly_than_chapest (start v : V) (d : ℕ)
(v_cost_is : g.cost_is start v d)
(w : g.Walk start v) :
    d ≤ w.cost := by
    unfold cost_is at v_cost_is
    obtain ⟨p,p_cost,p_cheapest⟩ := v_cost_is
    rw [←p_cost]
    unfold Path.is_cheapest at p_cheapest
    obtain ⟨w', w'_cheaper ⟩ := w.cheaper_path_exists
    apply le_trans
    · exact p_cheapest w'
    · exact w'_cheaper

section
variable (state : WeightedDiGraph.base_search_state g (ℕ×ℕ))

lemma astar_expand_keeps_stack_sorted (goal : V)
    :
     ∀ head : V, ∀ tail : List V,
        astar_stack_sorted heur state
          ∧ head ≠ goal
          ∧ state.stack = head :: tail
        → astar_stack_sorted  heur (hsearch_step_expand heur state head tail) := by
      intro head tail ⟨ prior_invar,head_ne_goal,compose⟩
      unfold astar_stack_sorted
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

lemma astar_expand_keeps_goal_invar (goal : V)
    :
     ∀ head : V, ∀ tail : List V,
        astar_goal_invar goal state
          ∧ head ≠ goal
          ∧ state.stack = head :: tail
        → astar_goal_invar goal (hsearch_step_expand heur state head tail) := by
  intro head tail ⟨ prior_invar, head_ne_goal, stack_compose ⟩
  unfold astar_goal_invar at prior_invar ⊢
  intro goal_visited
  unfold hsearch_step_expand at goal_visited ⊢
  simp at goal_visited ⊢
  cases goal_visited
  case inl goal_mem_tail =>
    left
    grind
  case inr _t =>
    right
    exact _t


lemma astar_expand_path_one_on_stack {head : V} {tail : List V} (goal v : V) (v_goal : g.Walk v goal) (v_visited : v ∈ state.visited) (v_not_on_stack : v ∉ state.stack)
  (stack_compose : state.stack = head :: tail)
  (on_stack_or_nei_visited : search_invar_on_stack_or_all_neighbours_visited state)
  (goal_invar : astar_goal_invar goal state)
  (head_not_mem_v_goal : head ∉ v_goal.support)
  :
  ∃ v' ∈ v_goal.support, v' ∈ (hsearch_step_expand heur state head tail).stack := by
    cases compose : v_goal
    · apply goal_invar at v_visited
      apply absurd v_visited v_not_on_stack
    case cons w adj_v_w w_goal =>
      have w_visited : w ∈ state.visited := by
        specialize on_stack_or_nei_visited ⟨ v, v_visited ⟩
        grind

      rw [compose] at head_not_mem_v_goal
      rw [Walk.support_cons] at head_not_mem_v_goal
      simp only [List.mem_cons, not_or] at head_not_mem_v_goal
      obtain ⟨head_ne_v,head_not_mem_w_goal ⟩ := head_not_mem_v_goal

      have w_ne_head : w ≠ head := by
        by_contra
        have head_mem_supp : head ∈ w_goal.support := by
          subst this
          apply Walk.start_in_support w_goal
        contradiction
      by_cases w_on_stack : w ∈ state.stack
      · have w_mem_tail : w ∈ tail := by
          rw [stack_compose] at w_on_stack
          grind
        use w
        constructor
        · simp
        · unfold hsearch_step_expand
          simp
          left
          exact w_mem_tail
      ·
        obtain ⟨v',proof⟩ := by
          apply astar_expand_path_one_on_stack goal (v:=w) <;> try assumption

        use v'
        constructor
        · simp
          right
          exact proof.1
        · exact proof.2


lemma astar_expand_keeps_path_invar {start : V} (goal : V)
  (on_stack_or_nei_visited : search_invar_on_stack_or_all_neighbours_visited state)
  (goal_invar : astar_goal_invar goal state)
  (stack_visited : search_invar_stack_is_visited state)
    :
     ∀ head : V, ∀ tail : List V,
        astar_path_invar start goal state
          ∧ head ≠ goal
          ∧ state.stack = head :: tail
        → astar_path_invar start goal (hsearch_step_expand heur state head tail) := by
    intro head tail ⟨ prior_invar, head_ne_goal, stack_compose ⟩
    unfold astar_path_invar at prior_invar ⊢
    intro p
    specialize prior_invar p
    obtain ⟨v', v'_in_p, was_open ⟩ := prior_invar
    unfold node_open at was_open ⊢
    rw [stack_compose] at was_open
    cases was_open
    case head =>
      have head_visited : head ∈ state.visited := by
        apply stack_visited head
        rw [stack_compose]
        simp
      obtain ⟨start_head, head_goal, compose⟩ := p.val.split_at v'_in_p
      have head_goal_nodup : head_goal.support.Nodup := by
        have p_nodup := p.prop
        rw [←compose] at p_nodup
        rw [Walk.support_of_append] at p_nodup
        rw [Walk.support_last (p:=start_head)] at p_nodup
        unfold List.Nodup at p_nodup ⊢
        rw [List.append_assoc] at p_nodup
        rw [List.pairwise_append] at p_nodup
        have x := p_nodup.2.1
        convert x
        cases head_goal
        · simp
          grind
        · simp

      cases head_goal_compose : head_goal
      case nil =>
        contradiction -- (goal ≠ goal)
      case cons head' adj_head_head' head'_goal =>
        have head_ne_head' : head ≠ head' := by
          rw [head_goal_compose] at head_goal_nodup
          simp at head_goal_nodup
          have head_not_mem_head'_goal := head_goal_nodup.1
          by_contra
          subst this
          have head_mem_head'_goal : head ∈ head'_goal.support := by
            apply Walk.start_in_support

          contradiction
        have head'_in_p : head' ∈ p.support := by
          unfold Path.support
          rw [← compose]
          rw [Walk.support_of_append]
          rw [List.mem_append]
          right
          rw [head_goal_compose]
          simp
        by_cases head'_on_stack : head' ∈ tail
        · use head'
          constructor
          · exact head'_in_p
          · unfold hsearch_step_expand
            simp
            left
            exact head'_on_stack
        · by_cases head'_visited : head' ∈ state.visited
          ·
            obtain ⟨ v', proof ⟩ := by
              apply astar_expand_path_one_on_stack (goal := goal) (v:=head') <;> try assumption
              · rw [stack_compose]
                grind
              · rw [head_goal_compose] at head_goal_nodup
                simp at head_goal_nodup
                exact head_goal_nodup.1
            use v'
            constructor
            · unfold Path.support
              rw [← compose]
              rw [Walk.support_of_append]
              rw [List.mem_append]
              right
              rw [head_goal_compose]
              simp
              exact proof.1
            · exact proof.2
          · use head'
            constructor
            · exact head'_in_p
            · unfold hsearch_step_expand
              simp
              right
              grind
    case tail v'_in_tail =>
      use v'
      constructor
      · exact v'_in_p
      · unfold hsearch_step_expand
        simp
        left
        exact v'_in_tail

/-
PROBLEM
pathOrder is an upper bound on the true optimal cost: if the optimal cost from start
    to v is d, then d ≤ pathOrder(v).1. Equivalently, pathOrder(v).1 ≥ g(v).

PROVIDED SOLUTION
Extract the walk from start to v using `WeightedDiGraph.extract_path_to`. By `hsearch_path_extracted_not_longer_than_path_order`, this path has cost ≤ `(state.pathOrder v).1`. Since `d` is the cost of the cheapest path to `v` (from `hd`), `d` is ≤ the cost of any walk to `v` by `walk_more_costly_than_chapest`. Hence `d ≤ pathOrder`.
-/
lemma optimal_cost_le_pathOrder
    (mother_invar : search_invar_mother_is_visited state)
    (mother_adj : search_invar_mother_is_adjacent start state)
    (decreasing : search_invar_mother_decreasing_path_order start state)
    (diff_invar : hsearch_path_order_diff_by_edge_cost start state)
    (v : V) (hv : v ∈ state.visited)
    (d : ℕ) (hd : g.cost_is start v d) :
    d ≤ (state.pathOrder v).1 := by
  -- Since the extracted path's cost is less than or equal to the path order's first component, and d is the minimum cost, we have d ≤ (state.pathOrder v).1.
  have h_extracted_cost_le_path_order : (WeightedDiGraph.extract_path_to start v state hv mother_invar mother_adj decreasing).1.cost ≤ (state.pathOrder v).1 :=
    hsearch_path_extracted_not_longer_than_path_order start state mother_invar mother_adj decreasing diff_invar v hv
  obtain ⟨ w, hw₁, hw₂ ⟩ := hd;
  contrapose! h_extracted_cost_le_path_order;
  refine lt_of_lt_of_le h_extracted_cost_le_path_order ?_;
  convert hw₂ _;
  exact hw₁.symm


/-
PROBLEM
For visited v with cost_is(start, v, d), the new pathOrder after expansion is still ≥ d.
    Combined with pathOrder_mono, this shows pathOrder stays = d when it was already = d.

PROVIDED SOLUTION
For visited v with cost_is(start, v, d), we need d ≤ new_pathOrder(v).1.

Case 1: v not adj to head. new_pathOrder(v) = old_pathOrder(v). By optimal_cost_le_pathOrder, d ≤ old_pathOrder(v).1 = new_pathOrder(v).1. ✓

Case 2: v adj to head. new_pathOrder(v).1 = min(old.1, pathOrder(head).1 + edgeCost(head,v)).
- d ≤ old.1 by optimal_cost_le_pathOrder. ✓ for old.
- d ≤ pathOrder(head).1 + edgeCost(head,v):
  - head is visited (by stack_visited since head ∈ stack).
  - Extract a path from start to head: by extract_path_to, cost ≤ pathOrder(head).1.
  - Concatenate with edge head→v: walk from start to v with cost ≤ pathOrder(head).1 + edgeCost.
  - d is the cheapest path cost, so d ≤ any walk cost ≤ pathOrder(head).1 + edgeCost. ✓
- So d ≤ min(old.1, pathOrder(head).1 + edgeCost) = new_pathOrder(v).1. ✓

For the walk argument: use walk_more_costly_than_chapest with the concatenated walk.

Actually, the walk needs to be constructed. We can use extract_path_to to get a path from start to head, then use Walk.concat to append the edge, getting a walk from start to v. Then walk_more_costly_than_chapest gives d ≤ this walk's cost = extracted.cost + edgeCost ≤ pathOrder(head) + edgeCost.
-/
lemma pathOrder_ge_optimal_after_expand
    (mother_invar : search_invar_mother_is_visited state)
    (mother_adj : search_invar_mother_is_adjacent start state)
    (decreasing : search_invar_mother_decreasing_path_order start state)
    (diff_invar : hsearch_path_order_diff_by_edge_cost start state)
    (stack_visited : search_invar_stack_is_visited state)
    :
    ∀ head : V, ∀ tail : List V,
      state.stack = head :: tail
      → ∀ v : V, v ∈ state.visited → ∀ d : ℕ, g.cost_is start v d →
        d ≤ ((hsearch_step_expand heur state head tail).pathOrder v).1 := by
  intros head tail hstack v hv d hd
  by_cases hv_adj_head : ∃ adj : g.Adj head v, True;
  · -- By definition of `extract_path_to`, there exists a walk from `start` to `head` with cost ≤ `pathOrder(head)`.
    have head_vis : head ∈ state.visited := stack_visited head (by rw [hstack]; simp)
    obtain ⟨walk_head, hwalk_head⟩ : ∃ walk_head : g.Walk start head, walk_head.cost ≤ (state.pathOrder head).1 := by
      let ep := WeightedDiGraph.extract_path_to start head state head_vis mother_invar mother_adj decreasing
      exact ⟨ep.1.val, hsearch_path_extracted_not_longer_than_path_order start state mother_invar mother_adj decreasing diff_invar head head_vis⟩
    -- By definition of `Walk.concat`, there exists a walk from `start` to `v` with cost ≤ `pathOrder(head) + edgeCost(head,v)`.
    obtain ⟨walk_v, hwalk_v⟩ : ∃ walk_v : g.Walk start v, walk_v.cost ≤ (state.pathOrder head).1 + g.edgeCost (hv_adj_head.choose) := by
      use walk_head.concat hv_adj_head.choose
      simp [Walk.concat];
      exact add_le_add hwalk_head le_rfl;
    have hwalk_v_min : d ≤ min ((state.pathOrder v).1) ((state.pathOrder head).1 + g.edgeCost (hv_adj_head.choose)) := by
      have hwalk_v_min : d ≤ walk_v.cost := by
        have hwalk_v_cost : ∀ p : g.Path start v, p.cost ≥ d := by
          intro p; exact (by
          obtain ⟨ p', hp' ⟩ := hd;
          exact hp'.1 ▸ hp'.2 p |> le_trans ( by rfl ) |> le_trans <| by rfl;);
        have hwalk_v_cost : ∃ p : g.Path start v, p.val.cost ≤ walk_v.cost := by
          obtain ⟨p', hp'⟩ := walk_v.cheaper_path_exists
          exact ⟨p', by unfold Path.cost at hp'; exact hp'⟩
        generalize_proofs at *; (
        exact le_trans ( by solve_by_elim ) hwalk_v_cost.choose_spec)
      generalize_proofs at *; (
      apply le_min
      exact optimal_cost_le_pathOrder state mother_invar mother_adj decreasing diff_invar v hv d hd
      exact hwalk_v_min.trans hwalk_v)
    unfold hsearch_step_expand
    simp only [new_cost]
    split_ifs <;> simp_all [path_val]
  · -- Since v is not adjacent to head, the pathOrder of v remains the same after expansion.
    have h_pathOrder_eq : ((hsearch_step_expand heur state head tail).pathOrder v).1 = (state.pathOrder v).1 := by
      unfold hsearch_step_expand; grind
    rw [h_pathOrder_eq]
    exact optimal_cost_le_pathOrder state mother_invar mother_adj decreasing diff_invar v hv d hd

/-
PROBLEM
Given a closed node w with optimal pathOrder on a Walk w_v from w to v (which is the suffix
    of a cheapest path p from start to v), find an open node on the walk with optimal pathOrder.

PROVIDED SOLUTION
start_w'_walk = start_w.concat adj_w_w' = start_w.append (cons adj nil). Unfold concat and use induction on start_w for append associativity. Then (cons adj nil).append rest = cons adj rest by definition. So start_w'_walk.append rest = start_w.append (cons adj rest) = p.val by hcompose.

We need cost_is(start, w', pathOrder(w).1 + edgeCost). From hw_cost_is, there exists a cheapest path from start to w with cost = pathOrder(w).1. Call this path q. Also, start_w'_walk is a walk from start to w' (through w). By subpath_of_cheapest_is_cheapest applied to p with the prefix start_w'_walk and suffix rest, the path ⟨start_w'_walk, nodup⟩ is cheapest. Its cost = cost of start_w + edgeCost = g(w) + edgeCost.

More precisely: we have start_w'_suffix : start_w'_walk.append rest = p.val. The prefix start_w'_walk has nodup (from p being a Path with nodup support). By subpath_of_cheapest_is_cheapest, ⟨start_w'_walk, nodup⟩ is cheapest. Its cost is start_w.cost + edgeCost (by concat_inc_cost_by_edge or append_cost).

But we also need to relate start_w.cost to pathOrder(w).1. From hw_cost_is: cost_is(start, w, pathOrder(w).1), meaning there exists a cheapest path from start to w with cost pathOrder(w).1. The subpath from start to w on p (which is start_w) has cost = g(w) = pathOrder(w).1 (since p is cheapest, its prefix is cheapest, and hw_cost_is gives the optimal cost).

So: cost of start_w'_walk = cost of start_w + edgeCost = pathOrder(w).1 + edgeCost.

And start_w'_walk is cheapest (by subpath_of_cheapest_is_cheapest). So cost_is holds.

start_w'_walk = start_w.concat adj_w_w'. By definition, Walk.concat p h = p.append (cons h nil). So start_w'_walk = start_w.append (cons adj_w_w' nil). Then start_w'_walk.append rest = (start_w.append (cons adj_w_w' nil)).append rest. Walk.append is associative by structural induction on the first walk (induction on start_w). So this equals start_w.append ((cons adj_w_w' nil).append rest). And (cons adj_w_w' nil).append rest = cons adj_w_w' (nil.append rest) = cons adj_w_w' rest by definition of append. So start_w'_walk.append rest = start_w.append (cons adj_w_w' rest) = p.val by hcompose.

Use subpath_of_cheapest_is_cheapest. We have:
- start_w'_suffix : start_w'_walk.append rest = p.val (the decomposition)
- hp : p.is_cheapest
- start_w'_walk is a Walk from start to w'
- rest is a Walk from w' to v

So the prefix start_w'_walk is a cheapest path from start to w'. Its cost = start_w.cost + edgeCost(w, w') (by Walk.concat_inc_cost_by_edge).

From hw_cost_is: cost_is start w (pathOrder w).1, meaning there's a cheapest path from start to w with cost = pathOrder(w).1. Since the subpath start_w from start to w on p is cheapest (by subpath_of_cheapest_is_cheapest applied with hcompose), start_w.cost = pathOrder(w).1 (both equal g(w)).

So start_w'_walk.cost = pathOrder(w).1 + edgeCost.

By subpath_of_cheapest_is_cheapest with start_w'_suffix and hp, ⟨start_w'_walk, nodup⟩ is cheapest with cost = pathOrder(w).1 + edgeCost. So cost_is holds.

For nodup: start_w'_walk.support is Nodup since it's a prefix of p.val which has Nodup support (Walk.nodup_prefix_of_append_nodup).
-/
lemma find_open_on_walk_suffix
    {s : WeightedDiGraph.base_search_state g (ℕ×ℕ)}
    (on_stack_or_nei : search_invar_on_stack_or_all_neighbours_visited s)
    (closed_bound_s : hsearch_invar_on_stack_or_all_neighbours_max_order s)
    (pathOrder_ge_g : ∀ u : V, u ∈ s.visited → ∀ d : ℕ, g.cost_is start u d → d ≤ (s.pathOrder u).1)
    {w v : V} (w_v : g.Walk w v)
    (hv_not_closed : ¬ node_closed s v)
    {p : g.Path start v} (hp : p.is_cheapest)
    (hw_on_p : w ∈ p.support)
    (w_v_is_suffix : ∃ start_w : g.Walk start w, start_w.append w_v = p.val)
    (hw_closed : node_closed s w)
    (hw_cost_is : g.cost_is start w (s.pathOrder w).1) :
    ∃ v' ∈ w_v.support, node_open s v' ∧ g.cost_is start v' (s.pathOrder v').1 := by
  cases w_v with
  | nil => exact absurd hw_closed hv_not_closed
  | cons adj_w_w' rest =>
    rename_i w'
    have w'_visited : w' ∈ s.visited := by
      have h := on_stack_or_nei ⟨w, hw_closed.1⟩
      rcases h with h_stack | h_nei
      · exact absurd h_stack hw_closed.2
      · exact h_nei w' adj_w_w'
    have bound : (s.pathOrder w').1 ≤ (s.pathOrder w).1 + g.edgeCost adj_w_w' :=
      closed_bound_s ⟨ w, hw_closed.1 ⟩ hw_closed.2 w' adj_w_w'
    obtain ⟨start_w, hcompose⟩ := w_v_is_suffix
    -- start_w.concat adj = start_w.append (cons adj nil)
    -- (start_w.concat adj).append rest = start_w.append (cons adj rest) = p.val
    have walk_append_assoc : ∀ {a b c d : V} (w1 : g.Walk a b) (w2 : g.Walk b c) (w3 : g.Walk c d),
        (w1.append w2).append w3 = w1.append (w2.append w3) := by
      intro a b c d w1 w2 w3
      induction w1 with
      | nil => simp [Walk.append]
      | cons h w1' ih => simp [Walk.append, ih]
    have concat_append : (start_w.concat adj_w_w').append rest = p.val := by
      unfold Walk.concat
      rw [walk_append_assoc]; simp [Walk.append]; exact hcompose
    -- start_w is a prefix of p with nodup
    have start_w_nodup : start_w.support.Nodup :=
      Walk.nodup_prefix_of_append_nodup start_w _ (hcompose ▸ p.prop)
    -- start_w' is a prefix of p with nodup
    have start_w'_nodup : (start_w.concat adj_w_w').support.Nodup :=
      Walk.nodup_prefix_of_append_nodup _ rest (concat_append ▸ p.prop)
    -- Subpath from start to w is cheapest
    have start_w_cheapest : WeightedDiGraph.Path.is_cheapest
        (⟨start_w, start_w_nodup⟩ : g.Path start w) :=
      WeightedDiGraph.Path.subpath_of_cheapest_is_cheapest p start_w
        (Walk.cons adj_w_w' rest) hcompose start_w_nodup hp
    -- start_w.cost = pathOrder(w).1 (both = g(w))
    have start_w_cost_eq : start_w.cost = (s.pathOrder w).1 := by
      obtain ⟨q, hq_cost, hq_cheapest⟩ := hw_cost_is
      have h1 : q.cost ≤ start_w.cost := by
        exact hq_cheapest ⟨start_w, start_w_nodup⟩
      have h2 : start_w.cost ≤ q.cost := by
        exact start_w_cheapest q
      rw [← hq_cost]; omega
    -- Subpath from start to w' is cheapest
    have start_w'_cheapest : WeightedDiGraph.Path.is_cheapest
        (⟨start_w.concat adj_w_w', start_w'_nodup⟩ : g.Path start w') :=
      WeightedDiGraph.Path.subpath_of_cheapest_is_cheapest p (start_w.concat adj_w_w')
        rest concat_append start_w'_nodup hp
    -- Cost of path to w'
    have start_w'_cost : (start_w.concat adj_w_w').cost = (s.pathOrder w).1 + g.edgeCost adj_w_w' := by
      rw [Walk.concat_inc_cost_by_edge, ← start_w_cost_eq, add_comm]
    -- cost_is for w'
    have w'_cost_is_d : g.cost_is start w' ((s.pathOrder w).1 + g.edgeCost adj_w_w') :=
      ⟨⟨start_w.concat adj_w_w', start_w'_nodup⟩, start_w'_cost, start_w'_cheapest⟩
    have ge : (s.pathOrder w).1 + g.edgeCost adj_w_w' ≤ (s.pathOrder w').1 :=
      pathOrder_ge_g w' w'_visited _ w'_cost_is_d
    have eq : (s.pathOrder w').1 = (s.pathOrder w).1 + g.edgeCost adj_w_w' := Nat.le_antisymm bound ge
    have w'_cost_is : g.cost_is start w' (s.pathOrder w').1 := eq ▸ w'_cost_is_d
    have w'_on_p : w' ∈ p.support := by
      unfold WeightedDiGraph.Path.support
      rw [← concat_append, Walk.support_of_append]
      apply List.mem_append_left
      exact Walk.goal_in_support (start_w.concat adj_w_w')
    by_cases w'_closed : node_closed s w'
    · obtain ⟨v', hv'_mem, hv'_open, hv'_cost⟩ := find_open_on_walk_suffix
        on_stack_or_nei closed_bound_s pathOrder_ge_g rest hv_not_closed hp
        w'_on_p ⟨start_w.concat adj_w_w', concat_append⟩ w'_closed w'_cost_is
      exact ⟨v', by rw [Walk.support_cons]; exact List.mem_cons_of_mem w hv'_mem,
             hv'_open, hv'_cost⟩
    · have w'_open : node_open s w' := by
        simp only [node_closed, not_and_or, Decidable.not_not] at w'_closed
        rcases w'_closed with h | h
        · exact absurd w'_visited h
        · exact h
      have w'_in_supp : w' ∈ (Walk.cons adj_w_w' rest).support := by
        rw [Walk.support_cons]; exact List.mem_cons_of_mem w (Walk.start_in_support rest)
      exact ⟨w', w'_in_supp, w'_open, w'_cost_is⟩

/-- Wrapper: find an open node on a cheapest path from a closed node with optimal pathOrder. -/
lemma find_open_on_path_from_closed
    {s : WeightedDiGraph.base_search_state g (ℕ×ℕ)}
    (on_stack_or_nei : search_invar_on_stack_or_all_neighbours_visited s)
    (closed_bound_s : hsearch_invar_on_stack_or_all_neighbours_max_order s)
    (pathOrder_ge_g : ∀ v : V, v ∈ s.visited → ∀ d : ℕ, g.cost_is start v d → d ≤ (s.pathOrder v).1)
    {v : V} (hv_not_closed : ¬ node_closed s v)
    {p : g.Path start v} (hp : p.is_cheapest)
    {w : V} (hw_on_p : w ∈ p.support) (hw_ne_v : w ≠ v)
    (hw_closed : node_closed s w)
    (hw_cost_is : g.cost_is start w (s.pathOrder w).1) :
    ∃ v' ∈ p.support, node_open s v' ∧ g.cost_is start v' (s.pathOrder v').1 := by
  obtain ⟨start_w, w_v, hcompose⟩ := p.val.split_at hw_on_p
  obtain ⟨v', hv'_mem, hv'_open, hv'_cost⟩ := find_open_on_walk_suffix
    on_stack_or_nei closed_bound_s pathOrder_ge_g w_v hv_not_closed hp
    hw_on_p ⟨start_w, hcompose⟩ hw_closed hw_cost_is
  refine ⟨v', ?_, hv'_open, hv'_cost⟩
  unfold Path.support
  rw [← hcompose, Walk.support_of_append]
  cases w_v with
  | nil =>
    simp [Walk.support] at hv'_mem
    subst hv'_mem
    exact List.mem_append_left _ (Walk.goal_in_support start_w)
  | cons adj rest =>
    rw [Walk.support_cons] at hv'_mem
    cases hv'_mem with
    | head => exact List.mem_append_left _ (Walk.goal_in_support start_w)
    | tail _ h => exact List.mem_append_right _ h

/-
PROBLEM
The main invariant follows from the properties of the state (without needing the old invariant).

PROVIDED SOLUTION
For non-closed v with cheapest path p from start to v:
- If start is open (start ∈ s.stack): use start as v'. start ∈ p.support (start is always in the support of a path from start). And cost_is(start, start, 0) by cost_v_v. And pathOrder(start).1 = 0 by start_pathOrder_zero. Done.
- If start is not open but is visited: start is closed. pathOrder(start).1 = 0 = g(start). cost_is(start, start, 0) by cost_v_v. Since start_pathOrder_zero gives pathOrder.1 = 0, we get cost_is(start, start, pathOrder(start).1).
  Apply find_open_on_path_from_closed with w = start. Start is on p.support (always). Start ≠ v (if start = v, then v is non-closed; but start is closed, contradiction unless start is open). Start is closed. Done.
-/
lemma astar_invar_from_state_properties
    {s : WeightedDiGraph.base_search_state g (ℕ×ℕ)}
    (start_visited : start ∈ s.visited)
    (start_pathOrder_zero : (s.pathOrder start).1 = 0)
    (on_stack_or_nei : search_invar_on_stack_or_all_neighbours_visited s)
    (closed_bound_s : hsearch_invar_on_stack_or_all_neighbours_max_order s)
    (pathOrder_ge_g : ∀ v : V, v ∈ s.visited → ∀ d : ℕ, g.cost_is start v d → d ≤ (s.pathOrder v).1) :
    astar_invar start s := by
  intro v hv_not_closed p hp_cheapest
  by_cases hv_start : v = start
  generalize_proofs at *; (
  -- Since $v = start$, the path from $start$ to $v$ is just the start itself. Therefore, $start$ is the node we're looking for.
  use start
  simp [hv_start, start_pathOrder_zero] at *; (
  exact ⟨ hv_not_closed start_visited, by exact cost_v_v start ⟩));
  -- Since v is not closed, start is open and we can apply the finding open node from closed node lemma.
  by_cases hv_open : node_open s start;
  · refine ⟨ start, ?_, hv_open, by simpa [ start_pathOrder_zero ] using cost_v_v start ⟩
    exact WeightedDiGraph.Walk.start_in_support p.1
  · apply find_open_on_path_from_closed on_stack_or_nei closed_bound_s pathOrder_ge_g
    exact hv_not_closed
    exact hp_cheapest
    any_goals exact start
    all_goals generalize_proofs at *; simp_all +decide [ node_closed, node_open ]
    · exact Ne.symm hv_start;
    · exact cost_v_v start


/-- After expansion, the optimal cost is ≤ pathOrder for all visited nodes in the new state. -/
lemma pathOrder_ge_optimal_all_after_expand
    (mother_invar : search_invar_mother_is_visited state)
    (mother_adj : search_invar_mother_is_adjacent start state)
    (decreasing : search_invar_mother_decreasing_path_order start state)
    (diff_invar_h : hsearch_path_order_diff_by_edge_cost start state)
    (stack_visited : search_invar_stack_is_visited state)
    :
    ∀ head : V, ∀ tail : List V,
      state.stack = head :: tail →
      ∀ v : V, v ∈ (hsearch_step_expand heur state head tail).visited →
        ∀ d : ℕ, g.cost_is start v d → d ≤ ((hsearch_step_expand heur state head tail).pathOrder v).1 := by
  intro head tail hstack v hv d hd
  by_cases hv_old : v ∈ state.visited
  · exact pathOrder_ge_optimal_after_expand heur state mother_invar mother_adj decreasing diff_invar_h stack_visited head tail hstack v hv_old d hd
  · -- v is newly visited: adj(head, v) and pathOrder(v) = path_val
    have head_vis : head ∈ state.visited := stack_visited head (by rw [hstack]; simp)
    -- Build walk start → head → v
    -- v is adjacent to head
    have adj := newly_visited_adj_head heur state v hv hv_old
    -- pathOrder(v).1 = pathOrder(head).1 + edgeCost
    have po_eq := pathOrder_newly_visited (tail := tail) heur state v adj hv_old
    -- Build walk start → head → v
    set extracted := WeightedDiGraph.extract_path_to start head state head_vis mother_invar mother_adj decreasing
    have hwalk : extracted.1.cost ≤ (state.pathOrder head).1 :=
      hsearch_path_extracted_not_longer_than_path_order start state mother_invar mother_adj decreasing diff_invar_h head head_vis
    have d_le := walk_more_costly_than_chapest start v d hd (extracted.1.val.concat adj)
    have walk_cost : (extracted.1.val.concat adj).cost = g.edgeCost adj + extracted.1.val.cost :=
      Walk.concat_inc_cost_by_edge extracted.1.val adj
    rw [po_eq]
    unfold Path.cost at hwalk
    omega


lemma astar_expand_keeps_main_invar (goal : V)
    (base_invars : search_invar_all_basic start state)
    (diff_invar : hsearch_path_order_diff_by_edge_cost start state)
    (closed_bound : hsearch_invar_on_stack_or_all_neighbours_max_order state)
    (start_zero : hsearch_invar_start_path_order_zero_zero start state)
    :
     ∀ head : V, ∀ tail : List V,
          head ≠ goal
          ∧ state.stack = head :: tail
        → astar_invar start (hsearch_step_expand heur state head tail) := by
    intro head tail ⟨head_ne_goal, stack_compose⟩
    -- Extract properties from base_invars
    obtain ⟨stack_vis, mother_vis, mother_adj, mother_dec, on_stack_nei, start_vis⟩ := base_invars
    -- Get new base invars
    have new_base : search_invar_all_basic start (hsearch_step_expand heur state head tail) :=
      hsearch_expand_keeps_base_invars heur state head tail
        ⟨⟨stack_vis, mother_vis, mother_adj, mother_dec, on_stack_nei, start_vis⟩, head_ne_goal, stack_compose⟩
    obtain ⟨new_stack_vis, _, _, _, new_on_stack_nei, new_start_vis⟩ := new_base
    -- Start pathOrder.1 = 0 in new state
    have new_start_zero := hsearch_expand_start_path_order_zero_carries heur state start goal start_vis head tail ⟨ start_zero, head_ne_goal, stack_compose ⟩
    -- closed_neighbor_pathOrder_bound in new state
    have new_closed_bound := hsearch_expand_keeps_on_stack_or_nei_max_order heur state goal on_stack_nei head tail
      ⟨closed_bound, head_ne_goal, stack_compose⟩
    -- pathOrder_ge_optimal for all visited nodes in new state
    have new_pathOrder_ge := pathOrder_ge_optimal_all_after_expand heur state mother_vis mother_adj mother_dec diff_invar stack_vis
      head tail stack_compose
    -- Apply astar_invar_from_state_properties
    exact astar_invar_from_state_properties new_start_vis (by simp [new_start_zero]) new_on_stack_nei new_closed_bound new_pathOrder_ge

end

/-- Bundled invariant for the A* search. -/
abbrev astar_all_invar (start goal : V) (s : WeightedDiGraph.base_search_state g (ℕ×ℕ)) :=
  WeightedDiGraph.search_invar_all_basic start s
  ∧ hsearch_path_order_diff_by_edge_cost start s
  ∧ astar_invar start s
  ∧ astar_path_invar start goal s
  ∧ astar_stack_sorted heur s
  ∧ astar_goal_invar goal s
  ∧ hsearch_invar_on_stack_or_all_neighbours_max_order s
  ∧ hsearch_invar_start_path_order_zero_zero  start s

lemma astar_all_invar_holds_at_init (start goal : V) :
    astar_all_invar heur start goal (WeightedDiGraph.base_search_state_initial (G:=g) start (0,0)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact WeightedDiGraph.base_search_state_initial_all_basic_invars start (0,0)
  · intro mother_adj u hv u_ne_start
    unfold WeightedDiGraph.base_search_state_initial at hv
    simp at hv; subst hv; exact absurd rfl u_ne_start
  · exact astar_invar_holds_at_init start
  · intro p; use start; simp [node_open]
  · simp [astar_stack_sorted]
  · intro hv; simp at hv ⊢; exact hv
  · simp [hsearch_invar_on_stack_or_all_neighbours_max_order,WeightedDiGraph.base_search_state_initial]
  · simp [hsearch_invar_start_path_order_zero_zero]

/-- The bundled A* invariant is preserved by expansion. -/
lemma astar_all_invar_preserved :
    WeightedDiGraph.base_invar_carries_over_expand
      (G := g) (D := ℕ×ℕ) (state_type := WeightedDiGraph.base_search_state g (ℕ×ℕ))
      (hsearch_step_expand heur) goal (astar_all_invar heur start goal) := by
  intro s head tail ⟨⟨base_invars, diff, main, path_inv, sorted, goal_inv, closed_bd, start_zero⟩, head_ne_goal, stack_compose⟩
  obtain ⟨stack_vis, mother_vis, mother_adj, mother_dec, on_stack_nei, start_vis⟩ := base_invars
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hsearch_expand_keeps_base_invars heur s head tail
      ⟨⟨stack_vis, mother_vis, mother_adj, mother_dec, on_stack_nei, start_vis⟩, head_ne_goal, stack_compose⟩
  · exact hsearch_expand_keeps_on_path_order_diff heur s start goal stack_vis mother_adj mother_vis head tail
      ⟨diff, head_ne_goal, stack_compose⟩
  · exact astar_expand_keeps_main_invar heur s goal
      ⟨stack_vis, mother_vis, mother_adj, mother_dec, on_stack_nei, start_vis⟩
      diff closed_bd start_zero head tail
      ⟨head_ne_goal, stack_compose⟩
  · exact astar_expand_keeps_path_invar heur s goal on_stack_nei goal_inv stack_vis head tail
      ⟨path_inv, head_ne_goal, stack_compose⟩
  · exact astar_expand_keeps_stack_sorted heur s goal head tail
      ⟨sorted, head_ne_goal, stack_compose⟩
  · exact astar_expand_keeps_goal_invar heur s goal head tail
      ⟨goal_inv, head_ne_goal, stack_compose⟩
  · exact hsearch_expand_keeps_on_stack_or_nei_max_order heur s goal on_stack_nei head tail
      ⟨closed_bd, head_ne_goal, stack_compose⟩
  · exact hsearch_expand_start_path_order_zero_carries heur s start goal start_vis head tail
      ⟨start_zero, head_ne_goal, stack_compose⟩

lemma astar_open_node_with_lower_f (start goal : V) (s : WeightedDiGraph.base_search_state g (ℕ×ℕ))
  (is_admissible : g.admissible heur goal)
  (has_astar_invar : astar_invar start s)
  (has_path_invar : astar_path_invar start goal s)
  :
  ∀ p : g.Path start goal, p.is_cheapest →
    ∃ v' ∈ p.support, (node_open s v') ∧ (s.pathOrder v').1 + (heur v') ≤ p.cost
  := by
  intro p p_cheapest
  unfold astar_invar at has_astar_invar
  unfold astar_path_invar at has_path_invar
  obtain ⟨v', v'_in_p, v'_open⟩ := has_path_invar p

  specialize has_astar_invar v'
  unfold node_closed at has_astar_invar
  simp [v'_open] at has_astar_invar
  obtain ⟨start_v', v'_goal, compose⟩ := p.val.split_at v'_in_p
  have start_v'_nodup : start_v'.support.Nodup :=
    Walk.nodup_prefix_of_append_nodup start_v' v'_goal (compose ▸ p.prop)
  have start_v'_cheapest : Path.is_cheapest ⟨start_v', start_v'_nodup⟩ :=
    Path.subpath_of_cheapest_is_cheapest p start_v' v'_goal compose start_v'_nodup p_cheapest

  specialize has_astar_invar start_v' start_v'_nodup start_v'_cheapest

  obtain ⟨v'',v''_in_support,v''_open,v''_cost_is⟩ := has_astar_invar

  use v''
  and_intros
  · unfold Path.support
    rw [←compose]
    rw [Walk.support_of_append]
    rw [List.mem_append]
    left
    exact v''_in_support
  · exact v''_open
  · unfold Path.cost
    have v''_in_p : v'' ∈ p.support := by
      unfold Path.support
      exact Walk.mem_support_prefix_of_append start_v' v'_goal compose v'' v''_in_support
    obtain ⟨start_v'', v''_goal, compose⟩ := p.val.split_at v''_in_p

    rw [←compose]
    rw [Walk.append_cost]
    apply add_le_add
    · apply walk_more_costly_than_chapest
      exact v''_cost_is
    · unfold admissible at is_admissible
      specialize is_admissible v''
      unfold cost_ge at is_admissible

      -- subwalk of p
      have v''_goal_nodup : v''_goal.support.Nodup :=
        Walk.nodup_suffix_of_append_nodup start_v'' v''_goal (compose ▸ p.prop)
      specialize is_admissible ⟨v''_goal, v''_goal_nodup⟩
      apply is_admissible



@[simp]
theorem admissible_heur_zero_for_goal
    (is_admissible : g.admissible heur goal):
    heur goal = 0 := by
      specialize is_admissible goal (nil_path goal)
      rw [Path.cost_nil_zero] at is_admissible
      simp_all only [ge_iff_le, nonpos_iff_eq_zero]

/- -/
theorem astar_is_optimal (start : V) (goal : V)
    (is_admissible : g.admissible heur goal)
    (returned_path : Option.isSome (astar (g:=g) heur start goal)):
    ((astar (g:=g) heur start goal).get returned_path).is_cheapest := by
    let final : WeightedDiGraph.base_search_state g (ℕ×ℕ) × Bool := WeightedDiGraph.search_with_stack_step (goal:=goal) (start_state := WeightedDiGraph.base_search_state_initial start (0,0)) (hsearch_step_expand heur) (hsearch_expand_metric_reduction heur)
    let final_state := final.1

    -- general properties
    have h_4 : WeightedDiGraph.search_prop_stack_head_is_goal goal final_state := by
      --intro terminated_with_goal_found
      --unfold search_prop_stack_head_is_goal
      unfold final_state
      unfold final
      unfold WeightedDiGraph.search_with_stack_step
      simp
      unfold WeightedDiGraph.search_internal
      apply WeightedDiGraph.search_recurse_obtain_base_termination_property (G:=g) (D:=ℕ×ℕ) (T:=(Vector (WithTop (ℕ × ℕ)) g.nodeNum) × ℕ) goal (WeightedDiGraph.base_search_state_initial start (0,0)) (property_after_termination := WeightedDiGraph.search_prop_stack_head_is_goal (D:=ℕ×ℕ) goal ) (terminated_with := true) (search_step := WeightedDiGraph.search_stack_step (G:=g) (D:=ℕ×ℕ) (hsearch_step_expand (g:=g) heur)) hsearch_termination_metric
      · intro s
        apply WeightedDiGraph.search_stack_step_goal_stack_head_if_terminated
      · unfold astar at returned_path
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

    -- Lift the bundled A* invariant to the final state
    have astar_full_invar_at_end : astar_all_invar heur start goal final_state := by
      have right_class : (fun s => astar_all_invar heur start goal
          (WeightedDiGraph.has_base_search_state.to_base_state (G:=g) s)) final_state := by
        unfold final_state
        unfold final
        unfold WeightedDiGraph.search_with_stack_step
        unfold WeightedDiGraph.search_internal
        simp
        apply WeightedDiGraph.search_recurse_lift_base_invariant
        constructor
        · exact astar_all_invar_holds_at_init heur start goal
        · apply WeightedDiGraph.base_invar_carries_over_stack_step
          exact astar_all_invar_preserved heur
      exact right_class

    have prop := hsearch_path_extracted_not_longer_than_path_order start final_state t_1 t_2 t_3
      astar_full_invar_at_end.2.1

    have has_astar_invar : astar_invar start final_state := astar_full_invar_at_end.2.2.1
    have has_astar_path_invar : astar_path_invar start goal final_state := astar_full_invar_at_end.2.2.2.1
    have xx := astar_open_node_with_lower_f heur start goal final_state is_admissible has_astar_invar


    apply Path.sufficient_cheapest_path_cheaper

    --unfold Path.is_cheapest
    intro p' p'_cheapest

    specialize xx has_astar_path_invar p' p'_cheapest

    obtain ⟨v', v'_on_p', v'_open,cost⟩ := xx

    apply le_trans ; rotate_left
    · apply cost
    · clear cost
      unfold astar search_exe_with_stack_step search_exe
      simp
      specialize prop goal h_3
      apply le_trans
      · apply prop
      · -- from invariant
        have final_stack_sorted : astar_stack_sorted heur final_state := astar_full_invar_at_end.2.2.2.2.1
        unfold astar_stack_sorted at final_stack_sorted
        unfold search_prop_stack_head_is_goal at h_4
        apply List.head?_eq_some_iff.mp at h_4
        obtain ⟨tail, compose⟩ := h_4
        unfold node_open at v'_open
        rw [compose] at final_stack_sorted v'_open
        rw [List.pairwise_cons] at final_stack_sorted
        obtain ⟨tail_larger, _⟩ := final_stack_sorted
        cases v'_open
        · apply Nat.le_add_right
        · next v'_in_tail =>
          specialize tail_larger v' v'_in_tail
          unfold add_heur at tail_larger
          rw [admissible_heur_zero_for_goal heur is_admissible] at tail_larger
          simp only [add_zero] at tail_larger
          cases tail_larger
          case inl h =>
            apply le_of_eq
            exact (Prod.mk_inj.mp h).1
          case inr h =>
            unfold FValueComp.lt Nat.instFValueCompProd at h
            simp at h
            apply Prod.lex_iff.mp at h
            cases h
            case inl h =>
              apply le_of_lt
              exact h
            case inr h =>
              apply le_of_eq
              exact h.1
end NatGraph


namespace NatGraph

variable (heur : V → ℕ)


def opt_heur : Option V → ℕ := fun v =>
    match v with
    | none => 0
    | some v' => heur v'

def astar_multigoal (start : V) (goals : List V): Option ((thegoal : {v : V // v ∈ goals}) × g.Path start thegoal) :=
  let nGraph : NatGraph (Option V) := g.add_artificial_goal goals
  let ret : Option (nGraph.Path start none) := nGraph.astar (opt_heur heur) start none

  match ret with
  | none => none
  | some p => by
    obtain ⟨w,⟨ path,prop⟩⟩ := WeightedDiGraph.Path.snoc p (by simp)
    have w_is_some : w.isSome := by
      unfold Option.isSome
      unfold nGraph NatGraph.add_artificial_goal at prop
      simp at prop
      grind
    let w' : V := w.get w_is_some
    have w_is_goal : w' ∈ goals := by
      unfold nGraph NatGraph.add_artificial_goal at prop
      simp at prop
      grind
    have w_eq_some_w' : w = Option.some w' := by grind
    have pp : none ∉ (w_eq_some_w' ▸ path).support := by apply none_not_in_walk_to_some
    have p : g.Path start w' := NatGraph.translate_path (G:=g) (w_eq_some_w' ▸ path) (pp)
    use Option.some ⟨⟨w',w_is_goal⟩,p⟩

theorem astar_multigoal_is_sound (start : V) (goals : List V) :
    (Option.isSome (astar_multigoal (g:=g) heur start goals) → (∃ goal ∈ goals, ∃ x : (g.Path start goal), x = x)) := by
    intro retSome
    let ret := g.astar_multigoal heur start goals
    let theGoal := (ret.get retSome).1
    let thePath := (ret.get retSome).2
    use theGoal
    constructor
    · exact theGoal.prop
    · constructor
      · rfl
      · use thePath
        exact thePath.prop


/-
PROVIDED SOLUTION
Given ∃ goal ∈ goals, ∃ x : g.Path start goal, x = x, obtain the goal and path p. By path_in_augmented_exists (using goal_in_goals and p), we get a path q from (some start) to none in the augmented graph g.add_artificial_goal goals. This means ∃ x : (g.add_artificial_goal goals).Path (some start) none, x = x. By astar_is_complete applied to the augmented graph (g.add_artificial_goal goals) with heuristic (opt_heur heur), start = (some start), goal = none, we get that astar returns Some on the augmented graph. Unfolding astar_multigoal, the match on the astar result in the Some case returns Some, so astar_multigoal returns Some, i.e. Option.isSome is true.
-/
theorem astar_multigoal_is_complete (start : V) (goals : List V):
    ((∃ goal ∈ goals, ∃ x : (g.Path start goal), x = x) → Option.isSome (astar_multigoal (g:=g) heur start goals)) := by
  contrapose!;
  intro h_contra goal hgoal x hx
  have h_path_in_augmented : ∃ q : (g.add_artificial_goal goals).Path (some start) none, q = q := by
    exact path_in_augmented_exists hgoal x;
  obtain ⟨ q, hq ⟩ := h_path_in_augmented;
  convert NatGraph.astar_is_complete ( g := g.add_artificial_goal goals ) ( opt_heur heur ) ( some start ) none _;
  · unfold astar_multigoal at h_contra
    simp_all only [ne_eq, Bool.not_eq_true, Option.isSome_eq_false_iff, Option.isNone_iff_eq_none, false_iff]
    obtain ⟨val, property⟩ := x
    obtain ⟨val_1, property_1⟩ := q
    split at h_contra
    next ret heq => simp_all only
    next ret p heq => simp_all only [reduceCtorEq]
  · exact ⟨ q, rfl ⟩

/-
PROBLEM
If admissible' holds on g, then opt_heur is admissible on the augmented graph for target none.

PROVIDED SOLUTION
We need to show: ∀ v : Option V, (g.add_artificial_goal goals).cost_ge v none (opt_heur heur v).

Unfolding cost_ge: ∀ p : (g.add_artificial_goal goals).Path v none, p.cost ≥ opt_heur heur v.

Case v = none: opt_heur heur none = 0, and p.cost ≥ 0 trivially for ℕ.

Case v = some v': opt_heur heur (some v') = heur v'. Let p be a path from (some v') to none. Since some v' ≠ none, use Path.split_at_end to decompose p = p' ++ [w_adj_none] where p' is a path from (some v') to w and w is adjacent to none. Since w is adjacent to none in add_artificial_goal, w must be some w' for some w' ∈ goals (by definition of add_artificial_goal, none has no outgoing edges and the only edges to none are from some g where g ∈ goals).

Now p' is a path from (some v') to (some w') with none ∉ p'.support (from split_at_end). Translate p' to get q : g.Path v' w' with q.cost = p'.cost (by translate_walk_cost_eq). Since w' ∈ goals and is_admissible says heur v' ≤ q.cost for all g.Path from v' to w', we get heur v' ≤ q.cost = p'.cost.

p.cost = p'.cost + edgeCost(w_adj_none). The edge from (some w') to none has cost 0 in add_artificial_goal. So p.cost = p'.cost + 0 = p'.cost ≥ heur v'.

To get p.cost from the split: use the fact that p.val = p'.val.concat w_adj_none, so p.cost = p'.cost + 0 by Walk.concat_inc_cost_by_edge and the fact that edgeCost of the artificial edge is 0.
-/
lemma opt_heur_admissible {goals : List V}
    (is_admissible : g.admissible' heur goals) :
    (g.add_artificial_goal goals).admissible (opt_heur heur) none := by
      intro v p
      by_cases hv : v = none
      · unfold opt_heur
        subst hv
        simp_all only [WeightedDiGraph.Path.cost_same, ge_iff_le, zero_le]
      · obtain ⟨ v', rfl ⟩ := Option.ne_none_iff_exists'.mp hv
        obtain ⟨w, hw⟩ : ∃ w : V, ∃ p' : (g.add_artificial_goal goals).Path (some v') (some w), ∃ w_adj_none : (g.add_artificial_goal goals).Adj w none, none∉ p'.support ∧ p.val = p'.val.concat w_adj_none := by
          obtain ⟨w, hw⟩ : ∃ w : Option V, ∃ p' : (g.add_artificial_goal goals).Path (some v') w, ∃ w_adj_none : (g.add_artificial_goal goals).Adj w none, none∉ p'.support ∧ p.val = p'.val.concat w_adj_none := by
            exact WeightedDiGraph.Path.split_at_end p hv;
          cases w <;> tauto;
        obtain ⟨ p', w_adj_none, hp'_none, hp_eq ⟩ := hw
        have h_cost_p' : p'.cost ≥ heur v' := by
          have h_cost_p' : ∃ q : g.Path v' w, q.cost = p'.cost := by
            exact ⟨ NatGraph.translate_path (G:=g) p' hp'_none, NatGraph.translate_walk_cost_eq _ hp'_none ⟩
          obtain ⟨ q, hq ⟩ := h_cost_p';
          exact le_of_le_of_eq (is_admissible v' w w_adj_none q) hq
        have h_cost_p : p.cost = p'.cost + (g.add_artificial_goal goals).edgeCost w_adj_none := by
          grind +suggestions
        rw [h_cost_p]
        simp
        exact le_add_right h_cost_p' |> le_trans ( by rfl )

/-
PROBLEM
When astar_multigoal returns some, the underlying astar also returns some.

PROVIDED SOLUTION
Unfold astar_multigoal. It matches on astar (opt_heur heur) (some start) none. If the astar returns none, then astar_multigoal returns none, contradicting returned_path. So astar must return some.
-/
lemma astar_multigoal_some_implies_astar_some (start : V) (goals : List V)
    (returned_path : Option.isSome (astar_multigoal (g:=g) heur start goals)) :
    Option.isSome (astar (g:=g.add_artificial_goal goals) (opt_heur heur) (some start) none) := by
      unfold astar_multigoal at returned_path
      simp_all only
      split at returned_path
      next ret heq => simp_all only [Option.isSome_none, Bool.false_eq_true]
      next ret p heq => simp_all only [Option.isSome_some]

/-
PROBLEM
The goal returned by astar_multigoal is in the goals list.

PROVIDED SOLUTION
Unfold astar_multigoal. In the some case, the returned goal is w' which was shown to be in goals (w_is_goal in the definition). The .1 of the returned value is w' which is in goals.
-/
lemma astar_multigoal_goal_in_goals (start : V) (goals : List V)
    (returned_path : Option.isSome (astar_multigoal (g:=g) heur start goals)) :
    ((astar_multigoal (g:=g) heur start goals).get returned_path).1.val ∈ goals := by
      have h_some : ∃ aug_path, astar (g:=g.add_artificial_goal goals) (opt_heur heur) (some start) none = some aug_path := by
        unfold astar_multigoal at returned_path
        cases h : astar (g:=g.add_artificial_goal goals) (opt_heur heur) (some start) none with
        | none => simp [h] at returned_path
        | some p => exact ⟨p, rfl⟩
      obtain ⟨aug_path, h_eq⟩ := h_some
      unfold astar_multigoal
      simp only [h_eq, Option.get_some]
      obtain ⟨w, path_to_w, w_adj_none⟩ := aug_path.snoc (by simp)
      simp only
      obtain ⟨w', hw_eq, hw_in⟩ := adj_to_none_is_goal (G:=g) w_adj_none
      subst hw_eq
      simp [hw_in]


/-- The cost of the returned multigoal path is ≤ the cost of the augmented A* path. -/
lemma astar_multigoal_cost_le_aug (start : V) (goals : List V)
    (returned_path : Option.isSome (astar_multigoal (g:=g) heur start goals))
    (aug_path : (g.add_artificial_goal goals).Path (some start) none)
    (h_eq : astar (g:=g.add_artificial_goal goals) (opt_heur heur) (some start) none = some aug_path) :
    ((astar_multigoal (g:=g) heur start goals).get returned_path).2.cost ≤ aug_path.cost := by
      delta astar_multigoal at returned_path ⊢
      dsimp only [] at returned_path ⊢
      revert returned_path
      rw [h_eq]
      intro returned_path
      simp only [Option.get_some]
      unfold translate_path WeightedDiGraph.Path.cost
      rw [translate_walk_cost_eq]
      rw [WeightedDiGraph.Path.path_subst_cost]
      unfold WeightedDiGraph.Path.snoc
      simp only
      -- Use the concat_eq from snoc_with_proof
      have concat_eq := (aug_path.val.snoc_with_proof
        (WeightedDiGraph.Walk.length_diff_ends_ne_zero (by simp) aug_path.val)).2.2.prop
      conv_rhs => rw [concat_eq]
      rw [WeightedDiGraph.Walk.concat_inc_cost_by_edge]
      apply Nat.le_add_left

theorem astar_multigoal_is_optimal (start : V) (goals : List V)
    (is_admissible : g.admissible' heur goals)
    (returned_path : Option.isSome (astar_multigoal (g:=g) heur start goals)):
    ((astar_multigoal (g:=g) heur start goals).get returned_path).2.is_cheapest := by
      -- Extract the augmented A* path
      have h_some : ∃ aug_path, astar (g:=g.add_artificial_goal goals) (opt_heur heur) (some start) none = some aug_path := by
        unfold astar_multigoal at returned_path
        cases h : astar (g:=g.add_artificial_goal goals) (opt_heur heur) (some start) none with
        | none => simp [h] at returned_path
        | some p => exact ⟨p, rfl⟩
      obtain ⟨aug_path, h_eq⟩ := h_some
      -- The augmented path is optimal
      have aug_optimal : aug_path.is_cheapest := by
        have aug_ret : Option.isSome (astar (g:=g.add_artificial_goal goals) (opt_heur heur) (some start) none) := by
          rw [h_eq]; simp
        have h := astar_is_optimal (g:=g.add_artificial_goal goals) (opt_heur heur) (some start) none
          (opt_heur_admissible heur is_admissible) aug_ret
        have h_get : (astar (g:=g.add_artificial_goal goals) (opt_heur heur) (some start) none).get aug_ret = aug_path := by
          simp [h_eq]
        rw [h_get] at h
        exact h
      -- Use sufficient_cheapest_path_cheaper
      apply WeightedDiGraph.Path.sufficient_cheapest_path_cheaper
      intro p' p'_cheapest
      -- thegoal ∈ goals
      have thegoal_in : ((astar_multigoal (g:=g) heur start goals).get returned_path).1.val ∈ goals :=
        astar_multigoal_goal_in_goals heur start goals returned_path
      -- Lift p' to the augmented graph
      obtain ⟨aug_p', h_cost_eq⟩ := lift_path_to_augmented_cost (G:=g) thegoal_in p'
      -- aug_path.cost ≤ p'.cost
      have h1 : aug_path.cost ≤ p'.cost := by
        calc aug_path.cost ≤ aug_p'.cost := aug_optimal aug_p'
          _ = p'.cost := h_cost_eq
      -- returned.cost ≤ aug_path.cost (from the helper lemma)
      have h2 := astar_multigoal_cost_le_aug heur start goals returned_path aug_path h_eq
      -- Combine
      exact le_trans h2 h1


end NatGraph
