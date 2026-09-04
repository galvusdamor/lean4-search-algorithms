import SearchAlgorithms.MultigoalHeap
import SearchAlgorithms.DijkstraHeapLazy

/-!
# Multi-goal search with a lazily deleted heap as search queue

`astar_multigoal_heap_lazy` and `dijkstra_multigoal_heap_lazy` are the multi-goal searches of
`SearchAlgorithms.MultigoalGen` run with `astar_heap_lazy`, i.e. with the lazily deleted heap
of `SearchAlgorithms.HeapLazyState`.

As before everything is transferred through `astar_heap_lazy_eq`, which says that the A* with
a lazily deleted heap returns literally the same path as the reference `astar`.  `te` is the
trace interval (`0` prints nothing); it defaults to `100`.
-/

namespace NatGraph

open WeightedDiGraph

variable {V : Type} [FinEnum V] [BEq V] [LawfulBEq V] [Hashable V]

/-- Multi-goal A* with a goal predicate, running on a generator graph with a lazily deleted
heap as search queue. -/
def astar_multigoal_heap_lazy (G : NatGraphWithGenerator V) (heur : V → ℕ∞) (start : V)
    (is_goal : V → Prop) [DecidablePred is_goal] (te : ℕ := 100) :
    Option ((thegoal : {v : V // is_goal v}) × (G.toWeightedDiGraph).Path start thegoal) :=
  astar_multigoal_postprocess (g := G.toWeightedDiGraph) start is_goal
    (astar_heap_lazy (add_artificial_goal_gen G is_goal) (opt_heur heur) (some start) none te)

/-- `astar_multigoal_heap_lazy` computes the same result as the enumeration-based
`astar_multigoal_aux`. -/
theorem astar_multigoal_heap_lazy_eq (G : NatGraphWithGenerator V) (heur : V → ℕ∞) (start : V)
    (is_goal : V → Prop) [DecidablePred is_goal] (te : ℕ) :
    astar_multigoal_heap_lazy G heur start is_goal te
      = astar_multigoal_aux (g := G.toWeightedDiGraph) heur start is_goal := by
  rw [astar_multigoal_aux_eq_postprocess]
  unfold astar_multigoal_heap_lazy
  rw [astar_heap_lazy_eq]
  rfl

/-- `astar_multigoal_heap_lazy` and `astar_multigoal_heap` return the same result. -/
theorem astar_multigoal_heap_lazy_eq_heap (G : NatGraphWithGenerator V) (heur : V → ℕ∞)
    (start : V) (is_goal : V → Prop) [DecidablePred is_goal] (te : ℕ) :
    astar_multigoal_heap_lazy G heur start is_goal te
      = astar_multigoal_heap G heur start is_goal := by
  rw [astar_multigoal_heap_lazy_eq, astar_multigoal_heap_eq]

/-- `astar_multigoal_heap_lazy` and `astar_multigoal_gen` return the same result. -/
theorem astar_multigoal_heap_lazy_eq_gen (G : NatGraphWithGenerator V) (heur : V → ℕ∞)
    (start : V) (is_goal : V → Prop) [DecidablePred is_goal] (te : ℕ) :
    astar_multigoal_heap_lazy G heur start is_goal te
      = astar_multigoal_gen G heur start is_goal := by
  rw [astar_multigoal_heap_lazy_eq, astar_multigoal_gen_eq]

theorem astar_multigoal_heap_lazy_is_sound (G : NatGraphWithGenerator V) (heur : V → ℕ∞)
    (start : V) (is_goal : V → Prop) [DecidablePred is_goal] (te : ℕ) :
    (Option.isSome (astar_multigoal_heap_lazy G heur start is_goal te) →
      (∃ goal : V, is_goal goal ∧ ∃ x : (G.toWeightedDiGraph).Path start goal, x = x)) := by
  rw [astar_multigoal_heap_lazy_eq]
  exact astar_multigoal_aux_is_sound heur start is_goal

theorem astar_multigoal_heap_lazy_is_complete (G : NatGraphWithGenerator V) (heur : V → ℕ∞)
    (start : V) (is_goal : V → Prop) [DecidablePred is_goal] (te : ℕ) :
    ((∃ goal : V, is_goal goal ∧
        ∃ p : (G.toWeightedDiGraph).Path start goal, ∀ u ∈ p.support, heur u ≠ ⊤) →
      Option.isSome (astar_multigoal_heap_lazy G heur start is_goal te)) := by
  rw [astar_multigoal_heap_lazy_eq]
  exact astar_multigoal_aux_is_complete heur start is_goal

/-- Optimality of the multi-goal A* with a lazily deleted heap: under an admissible heuristic
the returned path is a cheapest path to its goal. -/
theorem astar_multigoal_heap_lazy_is_optimal (G : NatGraphWithGenerator V) (heur : V → ℕ∞)
    (start : V) (is_goal : V → Prop) [DecidablePred is_goal] (te : ℕ)
    (is_admissible : admissible_pred (g := G.toWeightedDiGraph) heur is_goal)
    (returned_path : Option.isSome (astar_multigoal_heap_lazy G heur start is_goal te)) :
    ((astar_multigoal_heap_lazy G heur start is_goal te).get returned_path).2.is_cheapest := by
  revert returned_path
  rw [astar_multigoal_heap_lazy_eq]
  exact astar_multigoal_aux_is_optimal heur start is_goal is_admissible

/-! ### Multi-goal Dijkstra with a lazily deleted heap as search queue -/

/-- Multi-goal Dijkstra with a goal predicate, with a lazily deleted heap as search queue. -/
def dijkstra_multigoal_heap_lazy (G : NatGraphWithGenerator V) (start : V)
    (is_goal : V → Prop) [DecidablePred is_goal] (te : ℕ := 100) :
    Option ((thegoal : {v : V // is_goal v}) × (G.toWeightedDiGraph).Path start thegoal) :=
  astar_multigoal_heap_lazy G h_zero start is_goal te

theorem dijkstra_multigoal_heap_lazy_is_sound (G : NatGraphWithGenerator V) (start : V)
    (is_goal : V → Prop) [DecidablePred is_goal] (te : ℕ) :
    (Option.isSome (dijkstra_multigoal_heap_lazy G start is_goal te) →
      (∃ goal : V, is_goal goal ∧ ∃ x : (G.toWeightedDiGraph).Path start goal, x = x)) :=
  astar_multigoal_heap_lazy_is_sound G h_zero start is_goal te

/-- Multi-goal Dijkstra with a lazily deleted heap is complete: if some node satisfying
`is_goal` is reachable from `start`, it finds a path. -/
theorem dijkstra_multigoal_heap_lazy_is_complete (G : NatGraphWithGenerator V) (start : V)
    (is_goal : V → Prop) [DecidablePred is_goal] (te : ℕ) :
    ((∃ goal : V, is_goal goal ∧ ∃ p : (G.toWeightedDiGraph).Path start goal, p = p) →
      Option.isSome (dijkstra_multigoal_heap_lazy G start is_goal te)) := by
  rintro ⟨goal, hgoal, p, -⟩
  exact astar_multigoal_heap_lazy_is_complete G h_zero start is_goal te
    ⟨goal, hgoal, p, fun u _ => by simp only [h_zero]; exact WithTop.zero_ne_top⟩

/-- Multi-goal Dijkstra with a lazily deleted heap is optimal. -/
theorem dijkstra_multigoal_heap_lazy_is_optimal (G : NatGraphWithGenerator V) (start : V)
    (is_goal : V → Prop) [DecidablePred is_goal] (te : ℕ)
    (returned_path : Option.isSome (dijkstra_multigoal_heap_lazy G start is_goal te)) :
    ((dijkstra_multigoal_heap_lazy G start is_goal te).get returned_path).2.is_cheapest :=
  astar_multigoal_heap_lazy_is_optimal G h_zero start is_goal te
    (fun _ _ _ _ => by simp only [h_zero]; exact zero_le) returned_path

/-- `dijkstra_multigoal_heap_lazy` and `dijkstra_multigoal_heap` return the same result. -/
theorem dijkstra_multigoal_heap_lazy_eq_heap (G : NatGraphWithGenerator V) (start : V)
    (is_goal : V → Prop) [DecidablePred is_goal] (te : ℕ) :
    dijkstra_multigoal_heap_lazy G start is_goal te = dijkstra_multigoal_heap G start is_goal :=
  astar_multigoal_heap_lazy_eq_heap G h_zero start is_goal te

/-- `dijkstra_multigoal_heap_lazy` and `dijkstra_multigoal_gen` return the same result. -/
theorem dijkstra_multigoal_heap_lazy_eq_gen (G : NatGraphWithGenerator V) (start : V)
    (is_goal : V → Prop) [DecidablePred is_goal] (te : ℕ) :
    dijkstra_multigoal_heap_lazy G start is_goal te = dijkstra_multigoal_gen G start is_goal :=
  astar_multigoal_heap_lazy_eq_gen G h_zero start is_goal te

end NatGraph
