import SearchAlgorithms.MultigoalSorted
import SearchAlgorithms.DijkstraHeap

/-!
# Multi-goal search with a heap as search queue

`astar_multigoal_heap` and `dijkstra_multigoal_heap` are the multi-goal searches of
`SearchAlgorithms.MultigoalGen` run with `astar_heap`, i.e. with the search state of
`SearchAlgorithms.HeuristicSearchHeap`.

As before everything is transferred through `astar_heap_eq`, which says that the A* with a
heap queue returns literally the same path as the reference `astar`.
-/

namespace NatGraph

open WeightedDiGraph

variable {V : Type} [FinEnum V] [BEq V] [LawfulBEq V] [Hashable V]

/-- Multi-goal A* with a goal predicate, running on a generator graph with a heap as
search queue. -/
def astar_multigoal_heap (G : NatGraphWithGenerator V) (heur : V → ℕ∞) (start : V)
    (is_goal : V → Prop) [DecidablePred is_goal] :
    Option ((thegoal : {v : V // is_goal v}) × (G.toWeightedDiGraph).Path start thegoal) :=
  astar_multigoal_postprocess (g := G.toWeightedDiGraph) start is_goal
    (astar_heap (add_artificial_goal_gen G is_goal) (opt_heur heur) (some start) none)

/-- `astar_multigoal_heap` computes the same result as the enumeration-based
`astar_multigoal_aux`. -/
theorem astar_multigoal_heap_eq (G : NatGraphWithGenerator V) (heur : V → ℕ∞) (start : V)
    (is_goal : V → Prop) [DecidablePred is_goal] :
    astar_multigoal_heap G heur start is_goal
      = astar_multigoal_aux (g := G.toWeightedDiGraph) heur start is_goal := by
  rw [astar_multigoal_aux_eq_postprocess]
  unfold astar_multigoal_heap
  rw [astar_heap_eq]
  rfl

/-- `astar_multigoal_heap` and `astar_multigoal_sorted` return the same result. -/
theorem astar_multigoal_heap_eq_sorted (G : NatGraphWithGenerator V) (heur : V → ℕ∞) (start : V)
    (is_goal : V → Prop) [DecidablePred is_goal] :
    astar_multigoal_heap G heur start is_goal = astar_multigoal_sorted G heur start is_goal := by
  rw [astar_multigoal_heap_eq, astar_multigoal_sorted_eq]

/-- `astar_multigoal_heap` and `astar_multigoal_gen` return the same result. -/
theorem astar_multigoal_heap_eq_gen (G : NatGraphWithGenerator V) (heur : V → ℕ∞) (start : V)
    (is_goal : V → Prop) [DecidablePred is_goal] :
    astar_multigoal_heap G heur start is_goal = astar_multigoal_gen G heur start is_goal := by
  rw [astar_multigoal_heap_eq, astar_multigoal_gen_eq]

theorem astar_multigoal_heap_is_sound (G : NatGraphWithGenerator V) (heur : V → ℕ∞) (start : V)
    (is_goal : V → Prop) [DecidablePred is_goal] :
    (Option.isSome (astar_multigoal_heap G heur start is_goal) →
      (∃ goal : V, is_goal goal ∧ ∃ x : (G.toWeightedDiGraph).Path start goal, x = x)) := by
  rw [astar_multigoal_heap_eq]
  exact astar_multigoal_aux_is_sound heur start is_goal

theorem astar_multigoal_heap_is_complete (G : NatGraphWithGenerator V) (heur : V → ℕ∞)
    (start : V) (is_goal : V → Prop) [DecidablePred is_goal] :
    ((∃ goal : V, is_goal goal ∧
        ∃ p : (G.toWeightedDiGraph).Path start goal, ∀ u ∈ p.support, heur u ≠ ⊤) →
      Option.isSome (astar_multigoal_heap G heur start is_goal)) := by
  rw [astar_multigoal_heap_eq]
  exact astar_multigoal_aux_is_complete heur start is_goal

/-- Optimality of the multi-goal A* with a heap queue: under an admissible heuristic the returned path is
a cheapest path to its goal. -/
theorem astar_multigoal_heap_is_optimal (G : NatGraphWithGenerator V) (heur : V → ℕ∞)
    (start : V) (is_goal : V → Prop) [DecidablePred is_goal]
    (is_admissible : admissible_pred (g := G.toWeightedDiGraph) heur is_goal)
    (returned_path : Option.isSome (astar_multigoal_heap G heur start is_goal)) :
    ((astar_multigoal_heap G heur start is_goal).get returned_path).2.is_cheapest := by
  revert returned_path
  rw [astar_multigoal_heap_eq]
  exact astar_multigoal_aux_is_optimal heur start is_goal is_admissible

/-! ### Multi-goal Dijkstra with a heap as search queue -/

/-- Multi-goal Dijkstra with a goal predicate, with a heap as search queue. -/
def dijkstra_multigoal_heap (G : NatGraphWithGenerator V) (start : V)
    (is_goal : V → Prop) [DecidablePred is_goal] :
    Option ((thegoal : {v : V // is_goal v}) × (G.toWeightedDiGraph).Path start thegoal) :=
  astar_multigoal_heap G h_zero start is_goal

theorem dijkstra_multigoal_heap_is_sound (G : NatGraphWithGenerator V) (start : V)
    (is_goal : V → Prop) [DecidablePred is_goal] :
    (Option.isSome (dijkstra_multigoal_heap G start is_goal) →
      (∃ goal : V, is_goal goal ∧ ∃ x : (G.toWeightedDiGraph).Path start goal, x = x)) :=
  astar_multigoal_heap_is_sound G h_zero start is_goal

/-- Multi-goal Dijkstra with a heap as search queue is complete: if some node satisfying `is_goal`
is reachable from `start`, it finds a path. -/
theorem dijkstra_multigoal_heap_is_complete (G : NatGraphWithGenerator V) (start : V)
    (is_goal : V → Prop) [DecidablePred is_goal] :
    ((∃ goal : V, is_goal goal ∧ ∃ p : (G.toWeightedDiGraph).Path start goal, p = p) →
      Option.isSome (dijkstra_multigoal_heap G start is_goal)) := by
  rintro ⟨goal, hgoal, p, -⟩
  exact astar_multigoal_heap_is_complete G h_zero start is_goal
    ⟨goal, hgoal, p, fun u _ => by simp only [h_zero]; exact WithTop.zero_ne_top⟩

/-- Multi-goal Dijkstra with a heap as search queue is optimal. -/
theorem dijkstra_multigoal_heap_is_optimal (G : NatGraphWithGenerator V) (start : V)
    (is_goal : V → Prop) [DecidablePred is_goal]
    (returned_path : Option.isSome (dijkstra_multigoal_heap G start is_goal)) :
    ((dijkstra_multigoal_heap G start is_goal).get returned_path).2.is_cheapest :=
  astar_multigoal_heap_is_optimal G h_zero start is_goal
    (fun _ _ _ _ => by simp only [h_zero]; exact zero_le) returned_path

/-- `dijkstra_multigoal_heap` and `dijkstra_multigoal_sorted` return the same result. -/
theorem dijkstra_multigoal_heap_eq_sorted (G : NatGraphWithGenerator V) (start : V)
    (is_goal : V → Prop) [DecidablePred is_goal] :
    dijkstra_multigoal_heap G start is_goal = dijkstra_multigoal_sorted G start is_goal :=
  astar_multigoal_heap_eq_sorted G h_zero start is_goal

/-- `dijkstra_multigoal_heap` and `dijkstra_multigoal_gen` return the same result. -/
theorem dijkstra_multigoal_heap_eq_gen (G : NatGraphWithGenerator V) (start : V)
    (is_goal : V → Prop) [DecidablePred is_goal] :
    dijkstra_multigoal_heap G start is_goal = dijkstra_multigoal_gen G start is_goal :=
  astar_multigoal_heap_eq_gen G h_zero start is_goal

end NatGraph
