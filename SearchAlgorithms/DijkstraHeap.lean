import SearchAlgorithms.DijkstraSorted
import SearchAlgorithms.AStarHeap

/-!
# Dijkstra with a heap as search queue

`dijkstra_heap` is `astar_heap` with the zero heuristic, i.e. Dijkstra's algorithm running on
the search state of `SearchAlgorithms.HeuristicSearchHeap`: hash maps for the path order and
the mother relation, a hash-set backed visited set, a hash map of multiplicities for the
queue-membership test, and a leftist heap as the search queue.

Soundness, completeness and optimality come for free from `dijkstra`, via `dijkstra_heap_eq`.
-/

namespace NatGraph

open WeightedDiGraph

variable {V : Type} [FinEnum V] [BEq V] [LawfulBEq V] [Hashable V]
variable (G : NatGraphWithGenerator V)

/-- Dijkstra's algorithm with a heap as search queue. -/
def dijkstra_heap (start : V) (goal : V) : Option ((G.toWeightedDiGraph).Path start goal) :=
  astar_heap G h_zero start goal

/-- `dijkstra_heap` computes the same result as `dijkstra` on the underlying weighted
digraph. -/
theorem dijkstra_heap_eq (start : V) (goal : V) :
    dijkstra_heap G start goal = dijkstra (g := G.toWeightedDiGraph) start goal :=
  astar_heap_eq G h_zero start goal

theorem dijkstra_heap_is_sound (start : V) (goal : V) :
    (Option.isSome (dijkstra_heap G start goal)
      → (∃ x : ((G.toWeightedDiGraph).Path start goal), x = x)) := by
  rw [dijkstra_heap_eq]
  exact dijkstra_is_sound start goal

theorem dijkstra_heap_is_complete (start : V) (goal : V) :
    ((∃ x : ((G.toWeightedDiGraph).Path start goal), x = x)
      → Option.isSome (dijkstra_heap G start goal)) := by
  rw [dijkstra_heap_eq]
  exact dijkstra_is_complete start goal

/-- Optimality of `dijkstra_heap`: the returned path is a cheapest path to the goal. -/
theorem dijkstra_heap_is_optimal (start : V) (goal : V)
    (returned_path : Option.isSome (dijkstra_heap G start goal)) :
    ((dijkstra_heap G start goal).get returned_path).is_cheapest := by
  simp only [dijkstra_heap_eq] at returned_path ⊢
  exact dijkstra_is_optimal start goal returned_path

/-- `dijkstra_heap` and `dijkstra_sorted` return the same path. -/
theorem dijkstra_heap_eq_sorted (start : V) (goal : V) :
    dijkstra_heap G start goal = dijkstra_sorted G start goal := by
  rw [dijkstra_heap_eq, dijkstra_sorted_eq]

/-- `dijkstra_heap` and `dijkstra_gen` return the same path. -/
theorem dijkstra_heap_eq_gen (start : V) (goal : V) :
    dijkstra_heap G start goal = dijkstra_gen G start goal := by
  rw [dijkstra_heap_eq, dijkstra_gen_eq]

end NatGraph
