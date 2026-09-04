import SearchAlgorithms.MultigoalHeapLazy
import SearchAlgorithms.SearchExeFast

/-!
# The lazy-heap searches with linear-time path reconstruction

`astar_heap_lazy` (see `SearchAlgorithms.AStarHeapLazy`) is the fastest search of this
library, but like every other search here it rebuilds the answer with
`WeightedDiGraph.extract_path_to`, which is `Θ(L²)` in the length `L` of the returned path.
On a search whose answer is long, that reconstruction dominates the run time — on the
chain-broom benchmark of `BenchHeapLazy` the expansions cost 177 ms and the reconstruction
2846 ms.

This module runs the very same search with the linear reconstruction of
`SearchAlgorithms.ExtractPathFast`:

* `astar_heap_lazy_fastpath`, `dijkstra_heap_lazy_fastpath`,
  `astar_multigoal_heap_lazy_fastpath`, `dijkstra_multigoal_heap_lazy_fastpath`.

Nothing about the search itself changes — only the way the mother pointers are turned into a
path at the end — and `astar_heap_lazy_fastpath_eq` proves that the result is literally the
path returned by `astar_heap_lazy`, hence by `astar`.  Soundness, completeness and optimality
are therefore inherited without a new proof.
-/

namespace NatGraph

open WeightedDiGraph
open SearchAlgorithms

variable {V : Type} [FinEnum V] [BEq V] [LawfulBEq V] [Hashable V]
variable (G : NatGraphWithGenerator V) (heur : V → ℕ∞)

/-- **A\* with a lazily deleted heap and linear-time path reconstruction.**  The search is
`astar_heap_lazy`; only the reconstruction of the answer from the mother pointers differs
(`WeightedDiGraph.extract_path_fast` instead of `WeightedDiGraph.extract_path_to`). -/
def astar_heap_lazy_fastpath (start : V) (goal : V) (te : ℕ := 100) :
    Option ((G.toWeightedDiGraph).Path start goal) :=
  let start_state : hsearch_lazy_state V heur := hsearch_lazy_state.initial heur start ⟨0, 0⟩ te
  have h : WeightedDiGraph.has_base_search_state.to_base_state (G := G.toWeightedDiGraph)
      start_state = WeightedDiGraph.base_search_state_initial start (0, 0) :=
    hsearch_lazy_state.toBaseState_initial heur start (0, 0) te
  WeightedDiGraph.search_exe_with_step_eq_fast (G := G.toWeightedDiGraph) (start := start)
    (start_state := start_state)
    (termination_metric := hsearch_lazy_termination_metric G heur)
    (hsearch_step_expand_lazy G heur) goal
    (hsearch_lazy_step G heur) (hsearch_lazy_step_eq G heur)
    (hsearch_lazy_expand_metric_reduction G heur goal)
    (hsearch_lazy_expand_keeps_base_invars G heur start goal) h

/-- **`astar_heap_lazy_fastpath` returns the same path as `astar_heap_lazy`.** -/
theorem astar_heap_lazy_fastpath_eq_lazy (start : V) (goal : V) (te : ℕ) :
    astar_heap_lazy_fastpath G heur start goal te = astar_heap_lazy G heur start goal te :=
  WeightedDiGraph.search_exe_with_step_eq_fast_eq (G := G.toWeightedDiGraph) (start := start)
    (start_state := hsearch_lazy_state.initial heur start ⟨0, 0⟩ te)
    (termination_metric := hsearch_lazy_termination_metric G heur)
    (hsearch_step_expand_lazy G heur) goal
    (hsearch_lazy_step G heur) (hsearch_lazy_step_eq G heur)
    (hsearch_lazy_expand_metric_reduction G heur goal)
    (hsearch_lazy_expand_keeps_base_invars G heur start goal)
    (hsearch_lazy_state.toBaseState_initial heur start (0, 0) te)

/-- **`astar_heap_lazy_fastpath` computes the same result as `astar`.** -/
theorem astar_heap_lazy_fastpath_eq (start : V) (goal : V) (te : ℕ) :
    astar_heap_lazy_fastpath G heur start goal te
      = astar (g := G.toWeightedDiGraph) heur start goal := by
  rw [astar_heap_lazy_fastpath_eq_lazy, astar_heap_lazy_eq]

theorem astar_heap_lazy_fastpath_is_sound (start : V) (goal : V) (te : ℕ) :
    (Option.isSome (astar_heap_lazy_fastpath G heur start goal te)
      → (∃ x : ((G.toWeightedDiGraph).Path start goal), x = x)) := by
  rw [astar_heap_lazy_fastpath_eq]
  exact astar_is_sound heur start goal

/-- Completeness of `astar_heap_lazy_fastpath`: identical hypothesis to `astar_is_complete`. -/
theorem astar_heap_lazy_fastpath_is_complete (start : V) (goal : V) (te : ℕ) :
    ((∃ p : ((G.toWeightedDiGraph).Path start goal), ∀ u ∈ p.support, hsearch_expandable heur u)
      → Option.isSome (astar_heap_lazy_fastpath G heur start goal te)) := by
  rw [astar_heap_lazy_fastpath_eq]
  exact astar_is_complete heur start goal

/-- Optimality of `astar_heap_lazy_fastpath`: under an admissible heuristic the returned path
is a cheapest path to the goal. -/
theorem astar_heap_lazy_fastpath_is_optimal (start : V) (goal : V) (te : ℕ)
    (is_admissible : admissible (g := G.toWeightedDiGraph) heur goal)
    (returned_path : Option.isSome (astar_heap_lazy_fastpath G heur start goal te)) :
    ((astar_heap_lazy_fastpath G heur start goal te).get returned_path).is_cheapest := by
  simp only [astar_heap_lazy_fastpath_eq] at returned_path ⊢
  exact astar_is_optimal heur start goal is_admissible returned_path

/-! ### Dijkstra -/

/-- Dijkstra with a lazily deleted heap and linear-time path reconstruction. -/
def dijkstra_heap_lazy_fastpath (start : V) (goal : V) (te : ℕ := 100) :
    Option ((G.toWeightedDiGraph).Path start goal) :=
  astar_heap_lazy_fastpath G h_zero start goal te

/-- `dijkstra_heap_lazy_fastpath` computes the same result as `dijkstra`. -/
theorem dijkstra_heap_lazy_fastpath_eq (start : V) (goal : V) (te : ℕ) :
    dijkstra_heap_lazy_fastpath G start goal te = dijkstra (g := G.toWeightedDiGraph) start goal :=
  astar_heap_lazy_fastpath_eq G h_zero start goal te

theorem dijkstra_heap_lazy_fastpath_is_sound (start : V) (goal : V) (te : ℕ) :
    (Option.isSome (dijkstra_heap_lazy_fastpath G start goal te)
      → (∃ x : ((G.toWeightedDiGraph).Path start goal), x = x)) := by
  rw [dijkstra_heap_lazy_fastpath_eq]
  exact dijkstra_is_sound start goal

theorem dijkstra_heap_lazy_fastpath_is_complete (start : V) (goal : V) (te : ℕ) :
    ((∃ x : ((G.toWeightedDiGraph).Path start goal), x = x)
      → Option.isSome (dijkstra_heap_lazy_fastpath G start goal te)) := by
  rw [dijkstra_heap_lazy_fastpath_eq]
  exact dijkstra_is_complete start goal

/-- Optimality of `dijkstra_heap_lazy_fastpath`. -/
theorem dijkstra_heap_lazy_fastpath_is_optimal (start : V) (goal : V) (te : ℕ)
    (returned_path : Option.isSome (dijkstra_heap_lazy_fastpath G start goal te)) :
    ((dijkstra_heap_lazy_fastpath G start goal te).get returned_path).is_cheapest := by
  simp only [dijkstra_heap_lazy_fastpath_eq] at returned_path ⊢
  exact dijkstra_is_optimal start goal returned_path

/-! ### Multi-goal search -/

/-- Multi-goal A* with a lazily deleted heap and linear-time path reconstruction. -/
def astar_multigoal_heap_lazy_fastpath (start : V)
    (is_goal : V → Prop) [DecidablePred is_goal] (te : ℕ := 100) :
    Option ((thegoal : {v : V // is_goal v}) × (G.toWeightedDiGraph).Path start thegoal) :=
  astar_multigoal_postprocess (g := G.toWeightedDiGraph) start is_goal
    (astar_heap_lazy_fastpath (add_artificial_goal_gen G is_goal) (opt_heur heur) (some start)
      none te)

/-- `astar_multigoal_heap_lazy_fastpath` computes the same result as the enumeration-based
`astar_multigoal_aux`. -/
theorem astar_multigoal_heap_lazy_fastpath_eq (start : V)
    (is_goal : V → Prop) [DecidablePred is_goal] (te : ℕ) :
    astar_multigoal_heap_lazy_fastpath G heur start is_goal te
      = astar_multigoal_aux (g := G.toWeightedDiGraph) heur start is_goal := by
  unfold astar_multigoal_heap_lazy_fastpath
  rw [astar_heap_lazy_fastpath_eq_lazy]
  exact astar_multigoal_heap_lazy_eq G heur start is_goal te

theorem astar_multigoal_heap_lazy_fastpath_is_sound (start : V)
    (is_goal : V → Prop) [DecidablePred is_goal] (te : ℕ) :
    (Option.isSome (astar_multigoal_heap_lazy_fastpath G heur start is_goal te) →
      (∃ goal : V, is_goal goal ∧ ∃ x : (G.toWeightedDiGraph).Path start goal, x = x)) := by
  rw [astar_multigoal_heap_lazy_fastpath_eq]
  exact astar_multigoal_aux_is_sound heur start is_goal

theorem astar_multigoal_heap_lazy_fastpath_is_complete (start : V)
    (is_goal : V → Prop) [DecidablePred is_goal] (te : ℕ) :
    ((∃ goal : V, is_goal goal ∧
        ∃ p : (G.toWeightedDiGraph).Path start goal, ∀ u ∈ p.support, heur u ≠ ⊤) →
      Option.isSome (astar_multigoal_heap_lazy_fastpath G heur start is_goal te)) := by
  rw [astar_multigoal_heap_lazy_fastpath_eq]
  exact astar_multigoal_aux_is_complete heur start is_goal

/-- Optimality of the multi-goal A* with a lazily deleted heap and linear reconstruction. -/
theorem astar_multigoal_heap_lazy_fastpath_is_optimal (start : V)
    (is_goal : V → Prop) [DecidablePred is_goal] (te : ℕ)
    (is_admissible : admissible_pred (g := G.toWeightedDiGraph) heur is_goal)
    (returned_path : Option.isSome (astar_multigoal_heap_lazy_fastpath G heur start is_goal te)) :
    ((astar_multigoal_heap_lazy_fastpath G heur start is_goal te).get returned_path).2.is_cheapest := by
  revert returned_path
  rw [astar_multigoal_heap_lazy_fastpath_eq]
  exact astar_multigoal_aux_is_optimal heur start is_goal is_admissible

/-- Multi-goal Dijkstra with a lazily deleted heap and linear-time path reconstruction. -/
def dijkstra_multigoal_heap_lazy_fastpath (start : V)
    (is_goal : V → Prop) [DecidablePred is_goal] (te : ℕ := 100) :
    Option ((thegoal : {v : V // is_goal v}) × (G.toWeightedDiGraph).Path start thegoal) :=
  astar_multigoal_heap_lazy_fastpath G h_zero start is_goal te

theorem dijkstra_multigoal_heap_lazy_fastpath_is_sound (start : V)
    (is_goal : V → Prop) [DecidablePred is_goal] (te : ℕ) :
    (Option.isSome (dijkstra_multigoal_heap_lazy_fastpath G start is_goal te) →
      (∃ goal : V, is_goal goal ∧ ∃ x : (G.toWeightedDiGraph).Path start goal, x = x)) :=
  astar_multigoal_heap_lazy_fastpath_is_sound G h_zero start is_goal te

theorem dijkstra_multigoal_heap_lazy_fastpath_is_complete (start : V)
    (is_goal : V → Prop) [DecidablePred is_goal] (te : ℕ) :
    ((∃ goal : V, is_goal goal ∧ ∃ p : (G.toWeightedDiGraph).Path start goal, p = p) →
      Option.isSome (dijkstra_multigoal_heap_lazy_fastpath G start is_goal te)) := by
  rintro ⟨goal, hgoal, p, -⟩
  exact astar_multigoal_heap_lazy_fastpath_is_complete G h_zero start is_goal te
    ⟨goal, hgoal, p, fun u _ => by simp only [h_zero]; exact WithTop.zero_ne_top⟩

/-- Optimality of the multi-goal Dijkstra with a lazily deleted heap and linear
reconstruction. -/
theorem dijkstra_multigoal_heap_lazy_fastpath_is_optimal (start : V)
    (is_goal : V → Prop) [DecidablePred is_goal] (te : ℕ)
    (returned_path : Option.isSome (dijkstra_multigoal_heap_lazy_fastpath G start is_goal te)) :
    ((dijkstra_multigoal_heap_lazy_fastpath G start is_goal te).get returned_path).2.is_cheapest :=
  astar_multigoal_heap_lazy_fastpath_is_optimal G h_zero start is_goal te
    (fun _ _ _ _ => by simp only [h_zero]; exact zero_le) returned_path

end NatGraph
