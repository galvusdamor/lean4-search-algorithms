import SearchAlgorithms.Dijkstra
import SearchAlgorithms.HeuristicSearchGen

/-!
# Generator-based Dijkstra

This file defines `dijkstra_gen`, a version of `dijkstra` (see `SearchAlgorithms.Dijkstra`)
that runs on a `WeightedDiGraphWithGenerator`.  Like `astar_gen`, it is defined exactly like
`dijkstra`, but expands a node by iterating over its neighbour list instead of enumerating
all vertices of the graph.

Soundness, completeness and optimality are transferred from `dijkstra` via
`dijkstra_gen_eq : dijkstra_gen G start goal = dijkstra (g := G.toWeightedDiGraph) start goal`,
which itself follows from the one-step equivalence `hsearch_step_expand_gen_eq`.
-/

namespace NatGraph

open WeightedDiGraph

variable {V : Type} [FinEnum V]
variable (G : NatGraphWithGenerator V)

/-- Dijkstra's algorithm on a graph with an adjacency generator.  Identical to `dijkstra`
(the special case `h = 0` of A*), but expands nodes using the neighbour list instead of
enumerating all vertices. -/
def dijkstra_gen (start : V) (goal : V) : Option ((G.toWeightedDiGraph).Path start goal) :=
  let start_state := WeightedDiGraph.base_search_state_initial (G := G.toWeightedDiGraph) start ⟨0,0⟩
  have h : WeightedDiGraph.has_base_search_state.to_base_state (G:=G.toWeightedDiGraph) start_state
      = WeightedDiGraph.base_search_state_initial start (0,0) := by simp_all only [start_state]; rfl
  WeightedDiGraph.search_exe_with_stack_step (G:=G.toWeightedDiGraph) (start := start) (goal:=goal)
    (start_state:=start_state) (termination_metric := hsearch_termination_metric_nat)
    (hsearch_step_expand_gen G h_zero)
    (by rw [hsearch_step_expand_gen_eq_fun]; exact hsearch_expand_metric_reduction_nat h_zero)
    (by rw [hsearch_step_expand_gen_eq_fun]; exact hsearch_expand_keeps_base_invars h_zero) h

/-- `dijkstra_gen` computes the same result as `dijkstra` on the underlying weighted digraph. -/
theorem dijkstra_gen_eq (start : V) (goal : V) :
    dijkstra_gen G start goal = dijkstra (g := G.toWeightedDiGraph) start goal := by
  unfold dijkstra_gen dijkstra
  dsimp only
  -- First swap the cheap `nodeNum`-free metric back to the reference `Vector` metric (same
  -- generator step); the result is unchanged because the metric only steers termination.
  rw [search_exe_with_stack_step_metric_irrel
      (m := hsearch_termination_metric_nat (g := G.toWeightedDiGraph))
      (m' := hsearch_termination_metric (g := G.toWeightedDiGraph))
      (mp' := by rw [hsearch_step_expand_gen_eq_fun]; exact hsearch_expand_metric_reduction h_zero)]
  -- Then swap the generator step for the enumeration step (same `Vector` metric).
  exact search_exe_with_stack_step_congr (E := ℕ) (G := G.toWeightedDiGraph) (D := ℕ × ℕ)
    (state_type := hsearch_search_state G.toWeightedDiGraph)
    (termination_metric := hsearch_termination_metric (g := G.toWeightedDiGraph))
    (hsearch_step_expand_gen_eq_fun G h_zero) _ _ _ _ _ _

theorem dijkstra_gen_is_sound (start : V) (goal : V) :
    (Option.isSome (dijkstra_gen G start goal)
      → (∃ x : ((G.toWeightedDiGraph).Path start goal), x = x)) := by
  rw [dijkstra_gen_eq]
  exact dijkstra_is_sound start goal

theorem dijkstra_gen_is_complete (start : V) (goal : V) :
    ((∃ x : ((G.toWeightedDiGraph).Path start goal), x = x)
      → Option.isSome (dijkstra_gen G start goal)) := by
  rw [dijkstra_gen_eq]
  exact dijkstra_is_complete start goal

/-- Optimality of `dijkstra_gen`: the returned path is a cheapest path to the goal. -/
theorem dijkstra_gen_is_optimal (start : V) (goal : V)
    (returned_path : Option.isSome (dijkstra_gen G start goal)) :
    ((dijkstra_gen G start goal).get returned_path).is_cheapest := by
  simp only [dijkstra_gen_eq] at returned_path ⊢
  exact dijkstra_is_optimal start goal returned_path

end NatGraph
