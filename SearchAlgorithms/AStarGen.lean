import SearchAlgorithms.AStar
import SearchAlgorithms.HeuristicSearchGen

/-!
# Generator-based A*

This file defines `astar_gen`, a version of `astar` (see `SearchAlgorithms.AStar`) that
runs on a `WeightedDiGraphWithGenerator`.  It is defined exactly like `astar`, but uses
the generator-based expansion step `hsearch_step_expand_gen`, so it never enumerates the
whole vertex set: it expands a node by iterating over its neighbour list only.

Its soundness, completeness and optimality are obtained *for free* from the corresponding
results about `astar`, using `hsearch_step_expand_gen_eq` (one expansion step of the
generator-based search produces the same search state as one step of the original), which
implies `astar_gen G heur start goal = astar (g := G.toWeightedDiGraph) heur start goal`.
-/

namespace NatGraph

open WeightedDiGraph

variable {V : Type} [FinEnum V]
variable (G : NatGraphWithGenerator V) (heur : V → ℕ∞)

/-- The A* algorithm on a graph with an adjacency generator.  Identical to `astar`, but
expands nodes using the neighbour list instead of enumerating all vertices. -/
def astar_gen (start : V) (goal : V) : Option ((G.toWeightedDiGraph).Path start goal) :=
  let start_state := WeightedDiGraph.base_search_state_initial (G := G.toWeightedDiGraph) start ⟨0,0⟩
  have h : WeightedDiGraph.has_base_search_state.to_base_state (G:=G.toWeightedDiGraph) start_state
      = WeightedDiGraph.base_search_state_initial start (0,0) := by simp_all only [start_state]; rfl
  WeightedDiGraph.search_exe_with_stack_step (G:=G.toWeightedDiGraph) (start := start) (goal:=goal)
    (start_state:=start_state) (termination_metric := hsearch_termination_metric_nat)
    (hsearch_step_expand_gen G heur)
    (by rw [hsearch_step_expand_gen_eq_fun]; exact hsearch_expand_metric_reduction_nat heur)
    (by rw [hsearch_step_expand_gen_eq_fun]; exact hsearch_expand_keeps_base_invars heur) h

/-- `astar_gen` computes the same result as `astar` on the underlying weighted digraph. -/
theorem astar_gen_eq (start : V) (goal : V) :
    astar_gen G heur start goal = astar (g := G.toWeightedDiGraph) heur start goal := by
  unfold astar_gen astar
  dsimp only
  -- First swap the cheap `nodeNum`-free metric back to the reference `Vector` metric (same
  -- generator step); the result is unchanged because the metric only steers termination.
  rw [search_exe_with_stack_step_metric_irrel
      (m := hsearch_termination_metric_nat (g := G.toWeightedDiGraph))
      (m' := hsearch_termination_metric (g := G.toWeightedDiGraph))
      (mp' := by rw [hsearch_step_expand_gen_eq_fun]; exact hsearch_expand_metric_reduction heur)]
  -- Then swap the generator step for the enumeration step (same `Vector` metric).
  exact search_exe_with_stack_step_congr (E := ℕ) (G := G.toWeightedDiGraph) (D := ℕ × ℕ)
    (state_type := hsearch_search_state G.toWeightedDiGraph)
    (termination_metric := hsearch_termination_metric (g := G.toWeightedDiGraph))
    (hsearch_step_expand_gen_eq_fun G heur) _ _ _ _ _ _

theorem astar_gen_is_sound (start : V) (goal : V) :
    (Option.isSome (astar_gen G heur start goal)
      → (∃ x : ((G.toWeightedDiGraph).Path start goal), x = x)) := by
  rw [astar_gen_eq]
  exact astar_is_sound heur start goal

/-- Completeness of `astar_gen`: identical hypothesis to `astar_is_complete` (a path all of
whose nodes have a finite heuristic value). -/
theorem astar_gen_is_complete (start : V) (goal : V) :
    ((∃ p : ((G.toWeightedDiGraph).Path start goal), ∀ u ∈ p.support, hsearch_expandable heur u)
      → Option.isSome (astar_gen G heur start goal)) := by
  rw [astar_gen_eq]
  exact astar_is_complete heur start goal

/-- Optimality of `astar_gen`: under an admissible heuristic, the returned path is a
cheapest path to the goal. -/
theorem astar_gen_is_optimal (start : V) (goal : V)
    (is_admissible : admissible (g := G.toWeightedDiGraph) heur goal)
    (returned_path : Option.isSome (astar_gen G heur start goal)) :
    ((astar_gen G heur start goal).get returned_path).is_cheapest := by
  simp only [astar_gen_eq] at returned_path ⊢
  exact astar_is_optimal heur start goal is_admissible returned_path

end NatGraph
