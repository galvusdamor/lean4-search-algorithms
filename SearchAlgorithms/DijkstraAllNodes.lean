/-
# Dijkstra to all nodes

The `dijkstra` algorithm in `Dijkstra.lean` stops as soon as a specific goal node has
been reached and returns a shortest path to it.  Dijkstra's algorithm is however more
general: it computes the shortest path *to every node*.

This file provides such a variant.  Following the standard trick, we run the existing,
goal-directed Dijkstra on the graph augmented with a fresh, *unreachable* artificial sink
node `none` (`add_artificial_goal (fun _ => False)`).  Because no node is connected to
`none`, the search never finds its goal and instead runs until the fringe is exhausted,
visiting every node reachable from `start`.  We then read the answer off the final search
state:

* `dijkstra_all_dist start v` is the length of a shortest path from `start` to `v`
  (or `⊤` if `v` is unreachable).
* `dijkstra_all_extract_path start v` extracts an actual shortest path, reusing the
  mother-pointer structure already stored in the search state, so that no quadratic
  amount of path data has to be materialised up front.
-/
import SearchAlgorithms.Dijkstra

variable {V : Type} [FinEnum V] [DecidableEq V]
variable {g : NatGraph V}

namespace NatGraph

open WeightedDiGraph

/-- If the goal is never reached, the stack-based search returns `false`. -/
lemma dijkstra_last_state_returned_false_of_not_visited (start goal : V)
    (h : goal ∉ (dijkstra_last_state (g:=g) start goal).1.visited) :
    (dijkstra_last_state (g:=g) start goal).2 = false := by
  by_contra hb
  simp only [Bool.not_eq_false] at hb
  apply h
  revert hb
  unfold dijkstra_last_state WeightedDiGraph.search_with_stack_step
  simp only []
  apply WeightedDiGraph.search_visited_goal_if_returned_true
    (start := start) (start_state := WeightedDiGraph.base_search_state_initial start (0,0))
    (expandable := hsearch_expandable h_zero)
  · rfl
  · apply WeightedDiGraph.base_invar_carries_over_stack_step
    apply hsearch_expand_keeps_base_invars
  · intro s g'
    apply WeightedDiGraph.search_stack_step_goal_on_stack_if_terminated

/-- If the goal is not in the visited set of the final search state, the search
terminated with an empty stack (it returned `false`, i.e. "not found"). -/
lemma dijkstra_last_state_stack_empty_of_not_visited (start goal : V)
    (h : goal ∉ (dijkstra_last_state (g:=g) start goal).1.visited) :
    (dijkstra_last_state (g:=g) start goal).1.stack = [] := by
  have hf := dijkstra_last_state_returned_false_of_not_visited (g:=g) start goal h
  revert hf
  unfold dijkstra_last_state WeightedDiGraph.search_with_stack_step
  simp only []
  apply WeightedDiGraph.search_empty_stack_if_returned_false_recurse
  intro s
  apply WeightedDiGraph.stack_step_stack_empty_if_terminated_without_goal

/-! ## The augmented graph and its exhausted search state -/

/-- The graph augmented with an unreachable artificial sink node `none`.  Since the goal
predicate is `fun _ => False`, no node has an edge to `none`, so a Dijkstra search with
goal `none` runs until the fringe is empty, visiting every reachable node. -/
def augmentedUnreachable (g : NatGraph V) : NatGraph (Option V) :=
  g.add_artificial_goal (fun _ => False)

/-- The final search state obtained by running Dijkstra on `augmentedUnreachable g` from
`some start` towards the unreachable goal `none`. -/
def dijkstra_all_final_state (start : V) :
    base_search_state (augmentedUnreachable g) (ℕ × ℕ) :=
  (dijkstra_last_state (g := augmentedUnreachable g) (some start) none).1

/-- The full Dijkstra invariant holds for the exhausted search state. -/
lemma dijkstra_all_final_state_full_invar (start : V) :
    dijkstra_all_invar (g := augmentedUnreachable g) (some start)
      (dijkstra_all_final_state (g:=g) start) :=
  dijkstra_last_state_full_invar (g := augmentedUnreachable g) (some start) none

/-
The artificial sink `none` is never visited: nothing is adjacent to it.
-/
lemma dijkstra_all_none_not_visited (start : V) :
    (none : Option V) ∉ (dijkstra_all_final_state (g:=g) start).visited := by
  intro h_none_in_visited
  have hadj := dijkstra_all_final_state_full_invar start |>.1.2.2.1
    ⟨none, h_none_in_visited⟩ (by simp)
  obtain ⟨_, _, hfalse⟩ := NatGraph.adj_to_none_is_goal hadj
  exact hfalse

/-- The exhausted search has an empty stack/fringe. -/
lemma dijkstra_all_stack_empty (start : V) :
    (dijkstra_all_final_state (g:=g) start).stack = [] := by
  exact dijkstra_last_state_stack_empty_of_not_visited (g := augmentedUnreachable g)
    (some start) none (dijkstra_all_none_not_visited (g:=g) start)

/-- Every node reachable from `start` is visited by the exhausted search. -/
lemma dijkstra_all_visited_of_path (start v : V) (p : g.Path start v) :
    (some v) ∈ (dijkstra_all_final_state (g:=g) start).visited := by
  have basic := (dijkstra_all_final_state_full_invar (g:=g) start).1
  apply WeightedDiGraph.search_termination_with_empty_stack_implies_goal_visited
    (start := some start) (goal := some v) (f := some start)
    (theWalk := lift_walk_to_augmented (is_goal := (fun _ => False)) p.val)
    (final_state := dijkstra_all_final_state (g:=g) start)
    (expandable := hsearch_expandable h_zero)
  · exact basic.2.2.2.2.2
  · exact dijkstra_all_stack_empty (g:=g) start
  · intro w _; simp
  · exact basic.2.2.2.2.1

/-- For every visited (i.e. reachable) node, the stored path order is exactly the
shortest-path cost in the original graph. -/
lemma dijkstra_all_cost_is (start v : V)
    (hv : (some v) ∈ (dijkstra_all_final_state (g:=g) start).visited) :
    g.cost_is start v ((dijkstra_all_final_state (g:=g) start).pathOrder (some v)).1 := by
  have hstk := dijkstra_all_stack_empty (g:=g) start
  have hc := (dijkstra_all_final_state_full_invar (g:=g) start).2.1 (some v) hv
    (Or.inl (by rw [hstk]; simp))
  unfold augmentedUnreachable at hc
  exact augmented_cost_is_some.mp hc

/-- A node is visited iff it is reachable from `start`. -/
lemma dijkstra_all_visited_iff (start v : V) :
    (some v) ∈ (dijkstra_all_final_state (g:=g) start).visited ↔ Nonempty (g.Path start v) := by
  constructor
  · intro hv
    obtain ⟨p, _, _⟩ := dijkstra_all_cost_is (g:=g) start v hv
    exact ⟨p⟩
  · rintro ⟨p⟩
    exact dijkstra_all_visited_of_path (g:=g) start v p

/-! ## Shortest path lengths to all nodes -/

/-- The length of a shortest path from `start` to `v` in `g`, or `⊤` if `v` is
unreachable. -/
def dijkstra_all_dist (start v : V) : ℕ∞ :=
  if (some v) ∈ (dijkstra_all_final_state (g:=g) start).visited then
    ((dijkstra_all_final_state (g:=g) start).pathOrder (some v)).1
  else
    ⊤

/-- The distance is `⊤` exactly for unreachable nodes. -/
theorem dijkstra_all_dist_eq_top_iff (start v : V) :
    dijkstra_all_dist (g:=g) start v = ⊤ ↔ ¬ Nonempty (g.Path start v) := by
  unfold dijkstra_all_dist
  by_cases hv : (some v) ∈ (dijkstra_all_final_state (g:=g) start).visited
  · rw [if_pos hv]
    constructor
    · intro htop; simp at htop
    · intro hno; exact absurd ((dijkstra_all_visited_iff (g:=g) start v).mp hv) hno
  · rw [if_neg hv]
    constructor
    · intro _ hp; exact hv ((dijkstra_all_visited_iff (g:=g) start v).mpr hp)
    · intro _; rfl

/-- For reachable nodes, the distance equals the cost of a cheapest path. -/
theorem dijkstra_all_dist_eq_cost (start v : V) (c : ℕ) :
    dijkstra_all_dist (g:=g) start v = (c : ℕ∞) ↔ g.cost_is start v c := by
  unfold dijkstra_all_dist
  by_cases hv : (some v) ∈ (dijkstra_all_final_state (g:=g) start).visited
  · rw [if_pos hv]
    have hcost := dijkstra_all_cost_is (g:=g) start v hv
    constructor
    · intro hc
      have heq : ((dijkstra_all_final_state (g:=g) start).pathOrder (some v)).1 = c := by
        exact_mod_cast hc
      rwa [heq] at hcost
    · intro hcis
      rw [cost_is_unique hcost hcis]
  · rw [if_neg hv]
    constructor
    · intro htop; simp at htop
    · intro hcis
      obtain ⟨p, _, _⟩ := hcis
      exact absurd ((dijkstra_all_visited_iff (g:=g) start v).mpr ⟨p⟩) hv

/-! ## Extracting actual shortest paths -/

/-- Extract a shortest path from `start` to `v` from the exhausted search state, by
following the mother pointers (in the augmented graph) and translating the result back to
the original graph.  Returns `none` exactly when `v` is unreachable. -/
def dijkstra_all_extract_path (start v : V) : Option (g.Path start v) :=
  if hv : (some v) ∈ (dijkstra_all_final_state (g:=g) start).visited then
    let fs := dijkstra_all_final_state (g:=g) start
    let basic := (dijkstra_all_final_state_full_invar (g:=g) start).1
    let aug := extract_path_to (some start) (some v) fs hv basic.2.1 basic.2.2.1 basic.2.2.2.1
    some (translate_path aug.1 (none_not_in_walk_to_some aug.1.val))
  else
    none

/-- The extraction returns `none` exactly for unreachable nodes. -/
theorem dijkstra_all_extract_path_eq_none_iff (start v : V) :
    dijkstra_all_extract_path (g:=g) start v = none ↔ ¬ Nonempty (g.Path start v) := by
  unfold dijkstra_all_extract_path
  by_cases hv : (some v) ∈ (dijkstra_all_final_state (g:=g) start).visited
  · rw [dif_pos hv]
    constructor
    · intro h; exact absurd h (Option.some_ne_none _)
    · intro hno; exact absurd ((dijkstra_all_visited_iff (g:=g) start v).mp hv) hno
  · rw [dif_neg hv]
    exact iff_of_true rfl (fun hp => hv ((dijkstra_all_visited_iff (g:=g) start v).mpr hp))

/-- For reachable nodes, the extraction returns a cheapest path whose cost is exactly the
computed distance. -/
theorem dijkstra_all_extract_path_spec (start v : V) (p : g.Path start v) :
    ∃ q : g.Path start v,
      dijkstra_all_extract_path (g:=g) start v = some q
        ∧ q.is_cheapest
        ∧ (q.cost : ℕ∞) = dijkstra_all_dist (g:=g) start v := by
  have hv : (some v) ∈ (dijkstra_all_final_state (g:=g) start).visited :=
    dijkstra_all_visited_of_path (g:=g) start v p
  have full := dijkstra_all_final_state_full_invar (g:=g) start
  have basic := full.1
  set aug := extract_path_to (some start) (some v) (dijkstra_all_final_state (g:=g) start) hv
      basic.2.1 basic.2.2.1 basic.2.2.2.1 with haug
  set q : g.Path start v := translate_path aug.1 (none_not_in_walk_to_some aug.1.val) with hq
  -- the extracted (translated) path has cost equal to the augmented path's cost
  have hqcost : q.cost = aug.1.cost := by
    rw [hq]; exact translate_path_cost aug.1 (none_not_in_walk_to_some aug.1.val)
  -- the extracted augmented path is no longer than the recorded path order
  have hle : aug.1.cost ≤ ((dijkstra_all_final_state (g:=g) start).pathOrder (some v)).1 := by
    rw [haug]
    exact hsearch_path_extracted_not_longer_than_path_order (some start)
      (dijkstra_all_final_state (g:=g) start) basic.2.1 basic.2.2.1 basic.2.2.2.1
      full.2.2.1 (some v) hv
  obtain ⟨p0, hp0cost, hp0cheap⟩ := dijkstra_all_cost_is (g:=g) start v hv
  -- q is cheapest
  have hcheap : q.is_cheapest := by
    intro p'
    calc q.cost = aug.1.cost := hqcost
      _ ≤ ((dijkstra_all_final_state (g:=g) start).pathOrder (some v)).1 := hle
      _ = p0.cost := hp0cost.symm
      _ ≤ p'.cost := hp0cheap p'
  -- q has cost exactly the recorded path order
  have hqeq : q.cost = ((dijkstra_all_final_state (g:=g) start).pathOrder (some v)).1 := by
    have hge : ((dijkstra_all_final_state (g:=g) start).pathOrder (some v)).1 ≤ q.cost := by
      calc ((dijkstra_all_final_state (g:=g) start).pathOrder (some v)).1
            = p0.cost := hp0cost.symm
        _ ≤ q.cost := hp0cheap q
    exact le_antisymm (hqcost ▸ hle) hge
  refine ⟨q, ?_, hcheap, ?_⟩
  · unfold dijkstra_all_extract_path
    rw [dif_pos hv]
  · unfold dijkstra_all_dist
    rw [if_pos hv, hqeq]

end NatGraph