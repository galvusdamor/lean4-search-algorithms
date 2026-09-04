import SearchAlgorithms.MultigoalSorted
import SearchAlgorithms.SearchExeFast

/-!
# The sorted-queue searches with linear-time path reconstruction

The same change as in `SearchAlgorithms.AStarHeapLazyPath`, applied to the searches of
`SearchAlgorithms.AStarSorted`: the search is unchanged, only the answer is rebuilt from the
mother pointers in `O(L)` (`WeightedDiGraph.extract_path_fast`) instead of `Θ(L²)`
(`WeightedDiGraph.extract_path_to`).

The sorted queue is the better choice when the queue is filled once and then drained in order
(the "broom" shape of `BenchBroom`), so it is worth having the fast reconstruction here too.

`astar_sorted_fastpath_eq_sorted` proves that the returned path is literally the one of
`astar_sorted`, hence of `astar`; soundness, completeness and optimality follow.
-/

namespace NatGraph

open WeightedDiGraph

variable {V : Type} [FinEnum V] [BEq V] [LawfulBEq V] [Hashable V]
variable (G : NatGraphWithGenerator V) (heur : V → ℕ∞)

/-- **A\* with a maintained sorted queue and linear-time path reconstruction.** -/
def astar_sorted_fastpath (start : V) (goal : V) :
    Option ((G.toWeightedDiGraph).Path start goal) :=
  let start_state : hsearch_sorted_state V heur := hsearch_sorted_state.initial heur start ⟨0, 0⟩
  have h : WeightedDiGraph.has_base_search_state.to_base_state (G := G.toWeightedDiGraph)
      start_state = WeightedDiGraph.base_search_state_initial start (0, 0) :=
    hsearch_sorted_state.toBaseState_initial heur start (0, 0)
  WeightedDiGraph.search_exe_with_stack_step_fast (G := G.toWeightedDiGraph) (start := start)
    (start_state := start_state)
    (termination_metric := hsearch_sorted_termination_metric G heur)
    (hsearch_step_expand_sorted G heur) goal
    (hsearch_sorted_expand_metric_reduction G heur goal)
    (hsearch_sorted_expand_keeps_base_invars G heur start goal) h

/-- **`astar_sorted_fastpath` returns the same path as `astar_sorted`.** -/
theorem astar_sorted_fastpath_eq_sorted (start : V) (goal : V) :
    astar_sorted_fastpath G heur start goal = astar_sorted G heur start goal :=
  WeightedDiGraph.search_exe_with_stack_step_fast_eq (G := G.toWeightedDiGraph) (start := start)
    (start_state := hsearch_sorted_state.initial heur start ⟨0, 0⟩)
    (termination_metric := hsearch_sorted_termination_metric G heur)
    (hsearch_step_expand_sorted G heur) goal
    (hsearch_sorted_expand_metric_reduction G heur goal)
    (hsearch_sorted_expand_keeps_base_invars G heur start goal)
    (hsearch_sorted_state.toBaseState_initial heur start (0, 0))

/-- **`astar_sorted_fastpath` computes the same result as `astar`.** -/
theorem astar_sorted_fastpath_eq (start : V) (goal : V) :
    astar_sorted_fastpath G heur start goal = astar (g := G.toWeightedDiGraph) heur start goal := by
  rw [astar_sorted_fastpath_eq_sorted, astar_sorted_eq]

theorem astar_sorted_fastpath_is_sound (start : V) (goal : V) :
    (Option.isSome (astar_sorted_fastpath G heur start goal)
      → (∃ x : ((G.toWeightedDiGraph).Path start goal), x = x)) := by
  rw [astar_sorted_fastpath_eq]
  exact astar_is_sound heur start goal

/-- Completeness of `astar_sorted_fastpath`: identical hypothesis to `astar_is_complete`. -/
theorem astar_sorted_fastpath_is_complete (start : V) (goal : V) :
    ((∃ p : ((G.toWeightedDiGraph).Path start goal), ∀ u ∈ p.support, hsearch_expandable heur u)
      → Option.isSome (astar_sorted_fastpath G heur start goal)) := by
  rw [astar_sorted_fastpath_eq]
  exact astar_is_complete heur start goal

/-- Optimality of `astar_sorted_fastpath` under an admissible heuristic. -/
theorem astar_sorted_fastpath_is_optimal (start : V) (goal : V)
    (is_admissible : admissible (g := G.toWeightedDiGraph) heur goal)
    (returned_path : Option.isSome (astar_sorted_fastpath G heur start goal)) :
    ((astar_sorted_fastpath G heur start goal).get returned_path).is_cheapest := by
  simp only [astar_sorted_fastpath_eq] at returned_path ⊢
  exact astar_is_optimal heur start goal is_admissible returned_path

/-! ### Dijkstra -/

/-- Dijkstra with a maintained sorted queue and linear-time path reconstruction. -/
def dijkstra_sorted_fastpath (start : V) (goal : V) :
    Option ((G.toWeightedDiGraph).Path start goal) :=
  astar_sorted_fastpath G h_zero start goal

/-- `dijkstra_sorted_fastpath` computes the same result as `dijkstra`. -/
theorem dijkstra_sorted_fastpath_eq (start : V) (goal : V) :
    dijkstra_sorted_fastpath G start goal = dijkstra (g := G.toWeightedDiGraph) start goal :=
  astar_sorted_fastpath_eq G h_zero start goal

theorem dijkstra_sorted_fastpath_is_sound (start : V) (goal : V) :
    (Option.isSome (dijkstra_sorted_fastpath G start goal)
      → (∃ x : ((G.toWeightedDiGraph).Path start goal), x = x)) := by
  rw [dijkstra_sorted_fastpath_eq]
  exact dijkstra_is_sound start goal

theorem dijkstra_sorted_fastpath_is_complete (start : V) (goal : V) :
    ((∃ x : ((G.toWeightedDiGraph).Path start goal), x = x)
      → Option.isSome (dijkstra_sorted_fastpath G start goal)) := by
  rw [dijkstra_sorted_fastpath_eq]
  exact dijkstra_is_complete start goal

/-- Optimality of `dijkstra_sorted_fastpath`. -/
theorem dijkstra_sorted_fastpath_is_optimal (start : V) (goal : V)
    (returned_path : Option.isSome (dijkstra_sorted_fastpath G start goal)) :
    ((dijkstra_sorted_fastpath G start goal).get returned_path).is_cheapest := by
  simp only [dijkstra_sorted_fastpath_eq] at returned_path ⊢
  exact dijkstra_is_optimal start goal returned_path

/-! ### Multi-goal search -/

/-- Multi-goal A* with a maintained sorted queue and linear-time path reconstruction. -/
def astar_multigoal_sorted_fastpath (start : V)
    (is_goal : V → Prop) [DecidablePred is_goal] :
    Option ((thegoal : {v : V // is_goal v}) × (G.toWeightedDiGraph).Path start thegoal) :=
  astar_multigoal_postprocess (g := G.toWeightedDiGraph) start is_goal
    (astar_sorted_fastpath (add_artificial_goal_gen G is_goal) (opt_heur heur) (some start) none)

/-- `astar_multigoal_sorted_fastpath` computes the same result as the enumeration-based
`astar_multigoal_aux`. -/
theorem astar_multigoal_sorted_fastpath_eq (start : V)
    (is_goal : V → Prop) [DecidablePred is_goal] :
    astar_multigoal_sorted_fastpath G heur start is_goal
      = astar_multigoal_aux (g := G.toWeightedDiGraph) heur start is_goal := by
  unfold astar_multigoal_sorted_fastpath
  rw [astar_sorted_fastpath_eq_sorted]
  exact astar_multigoal_sorted_eq G heur start is_goal

theorem astar_multigoal_sorted_fastpath_is_sound (start : V)
    (is_goal : V → Prop) [DecidablePred is_goal] :
    (Option.isSome (astar_multigoal_sorted_fastpath G heur start is_goal) →
      (∃ goal : V, is_goal goal ∧ ∃ x : (G.toWeightedDiGraph).Path start goal, x = x)) := by
  rw [astar_multigoal_sorted_fastpath_eq]
  exact astar_multigoal_aux_is_sound heur start is_goal

theorem astar_multigoal_sorted_fastpath_is_complete (start : V)
    (is_goal : V → Prop) [DecidablePred is_goal] :
    ((∃ goal : V, is_goal goal ∧
        ∃ p : (G.toWeightedDiGraph).Path start goal, ∀ u ∈ p.support, heur u ≠ ⊤) →
      Option.isSome (astar_multigoal_sorted_fastpath G heur start is_goal)) := by
  rw [astar_multigoal_sorted_fastpath_eq]
  exact astar_multigoal_aux_is_complete heur start is_goal

/-- Optimality of the multi-goal A* with a sorted queue and linear reconstruction. -/
theorem astar_multigoal_sorted_fastpath_is_optimal (start : V)
    (is_goal : V → Prop) [DecidablePred is_goal]
    (is_admissible : admissible_pred (g := G.toWeightedDiGraph) heur is_goal)
    (returned_path : Option.isSome (astar_multigoal_sorted_fastpath G heur start is_goal)) :
    ((astar_multigoal_sorted_fastpath G heur start is_goal).get returned_path).2.is_cheapest := by
  revert returned_path
  rw [astar_multigoal_sorted_fastpath_eq]
  exact astar_multigoal_aux_is_optimal heur start is_goal is_admissible

/-- Multi-goal Dijkstra with a maintained sorted queue and linear-time path reconstruction. -/
def dijkstra_multigoal_sorted_fastpath (start : V)
    (is_goal : V → Prop) [DecidablePred is_goal] :
    Option ((thegoal : {v : V // is_goal v}) × (G.toWeightedDiGraph).Path start thegoal) :=
  astar_multigoal_sorted_fastpath G h_zero start is_goal

theorem dijkstra_multigoal_sorted_fastpath_is_sound (start : V)
    (is_goal : V → Prop) [DecidablePred is_goal] :
    (Option.isSome (dijkstra_multigoal_sorted_fastpath G start is_goal) →
      (∃ goal : V, is_goal goal ∧ ∃ x : (G.toWeightedDiGraph).Path start goal, x = x)) :=
  astar_multigoal_sorted_fastpath_is_sound G h_zero start is_goal

theorem dijkstra_multigoal_sorted_fastpath_is_complete (start : V)
    (is_goal : V → Prop) [DecidablePred is_goal] :
    ((∃ goal : V, is_goal goal ∧ ∃ p : (G.toWeightedDiGraph).Path start goal, p = p) →
      Option.isSome (dijkstra_multigoal_sorted_fastpath G start is_goal)) := by
  rintro ⟨goal, hgoal, p, -⟩
  exact astar_multigoal_sorted_fastpath_is_complete G h_zero start is_goal
    ⟨goal, hgoal, p, fun u _ => by simp only [h_zero]; exact WithTop.zero_ne_top⟩

/-- Optimality of the multi-goal Dijkstra with a sorted queue and linear reconstruction. -/
theorem dijkstra_multigoal_sorted_fastpath_is_optimal (start : V)
    (is_goal : V → Prop) [DecidablePred is_goal]
    (returned_path : Option.isSome (dijkstra_multigoal_sorted_fastpath G start is_goal)) :
    ((dijkstra_multigoal_sorted_fastpath G start is_goal).get returned_path).2.is_cheapest :=
  astar_multigoal_sorted_fastpath_is_optimal G h_zero start is_goal
    (fun _ _ _ _ => by simp only [h_zero]; exact zero_le) returned_path

end NatGraph
