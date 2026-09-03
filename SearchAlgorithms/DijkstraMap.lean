import SearchAlgorithms.DijkstraGen
import SearchAlgorithms.AStarMap

/-!
# Dijkstra on the flattened (hash-map) search state

`dijkstra_map` is `astar_map` with the zero heuristic, i.e. Dijkstra's algorithm running on
the flattened search state of `SearchAlgorithms.HeuristicSearchMap`.

Soundness, completeness and optimality come for free from `dijkstra`, via
`dijkstra_map_eq`.
-/

namespace NatGraph

open WeightedDiGraph

variable {V : Type} [FinEnum V] [BEq V] [LawfulBEq V] [Hashable V]
variable (G : NatGraphWithGenerator V)

/-- Dijkstra's algorithm with the flattened, hash-map based search state. -/
def dijkstra_map (start : V) (goal : V) : Option ((G.toWeightedDiGraph).Path start goal) :=
  astar_map G h_zero start goal

/-- `dijkstra_map` computes the same result as `dijkstra` on the underlying weighted digraph. -/
theorem dijkstra_map_eq (start : V) (goal : V) :
    dijkstra_map G start goal = dijkstra (g := G.toWeightedDiGraph) start goal :=
  astar_map_eq G h_zero start goal

theorem dijkstra_map_is_sound (start : V) (goal : V) :
    (Option.isSome (dijkstra_map G start goal)
      → (∃ x : ((G.toWeightedDiGraph).Path start goal), x = x)) := by
  rw [dijkstra_map_eq]
  exact dijkstra_is_sound start goal

theorem dijkstra_map_is_complete (start : V) (goal : V) :
    ((∃ x : ((G.toWeightedDiGraph).Path start goal), x = x)
      → Option.isSome (dijkstra_map G start goal)) := by
  rw [dijkstra_map_eq]
  exact dijkstra_is_complete start goal

/-- Optimality of `dijkstra_map`: the returned path is a cheapest path to the goal. -/
theorem dijkstra_map_is_optimal (start : V) (goal : V)
    (returned_path : Option.isSome (dijkstra_map G start goal)) :
    ((dijkstra_map G start goal).get returned_path).is_cheapest := by
  simp only [dijkstra_map_eq] at returned_path ⊢
  exact dijkstra_is_optimal start goal returned_path

/-- `dijkstra_map` and `dijkstra_gen` return the same path. -/
theorem dijkstra_map_eq_gen (start : V) (goal : V) :
    dijkstra_map G start goal = dijkstra_gen G start goal := by
  rw [dijkstra_map_eq, dijkstra_gen_eq]

end NatGraph
