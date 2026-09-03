import SearchAlgorithms.DijkstraMap
import SearchAlgorithms.AStarFast

/-!
# Dijkstra on the fast search state

`dijkstra_fast` is `astar_fast` with the zero heuristic, i.e. Dijkstra's algorithm running on
the search state of `SearchAlgorithms.HeuristicSearchFast` (hash maps for the path order and
the mother relation, hash-set backed visited set).

Soundness, completeness and optimality come for free from `dijkstra`, via `dijkstra_fast_eq`.
-/

namespace NatGraph

open WeightedDiGraph

variable {V : Type} [FinEnum V] [BEq V] [LawfulBEq V] [Hashable V]
variable (G : NatGraphWithGenerator V)

/-- Dijkstra's algorithm with the fast search state. -/
def dijkstra_fast (start : V) (goal : V) : Option ((G.toWeightedDiGraph).Path start goal) :=
  astar_fast G h_zero start goal

/-- `dijkstra_fast` computes the same result as `dijkstra` on the underlying weighted
digraph. -/
theorem dijkstra_fast_eq (start : V) (goal : V) :
    dijkstra_fast G start goal = dijkstra (g := G.toWeightedDiGraph) start goal :=
  astar_fast_eq G h_zero start goal

theorem dijkstra_fast_is_sound (start : V) (goal : V) :
    (Option.isSome (dijkstra_fast G start goal)
      → (∃ x : ((G.toWeightedDiGraph).Path start goal), x = x)) := by
  rw [dijkstra_fast_eq]
  exact dijkstra_is_sound start goal

theorem dijkstra_fast_is_complete (start : V) (goal : V) :
    ((∃ x : ((G.toWeightedDiGraph).Path start goal), x = x)
      → Option.isSome (dijkstra_fast G start goal)) := by
  rw [dijkstra_fast_eq]
  exact dijkstra_is_complete start goal

/-- Optimality of `dijkstra_fast`: the returned path is a cheapest path to the goal. -/
theorem dijkstra_fast_is_optimal (start : V) (goal : V)
    (returned_path : Option.isSome (dijkstra_fast G start goal)) :
    ((dijkstra_fast G start goal).get returned_path).is_cheapest := by
  simp only [dijkstra_fast_eq] at returned_path ⊢
  exact dijkstra_is_optimal start goal returned_path

/-- `dijkstra_fast` and `dijkstra_map` return the same path. -/
theorem dijkstra_fast_eq_map (start : V) (goal : V) :
    dijkstra_fast G start goal = dijkstra_map G start goal := by
  rw [dijkstra_fast_eq, dijkstra_map_eq]

/-- `dijkstra_fast` and `dijkstra_gen` return the same path. -/
theorem dijkstra_fast_eq_gen (start : V) (goal : V) :
    dijkstra_fast G start goal = dijkstra_gen G start goal := by
  rw [dijkstra_fast_eq, dijkstra_gen_eq]

end NatGraph
