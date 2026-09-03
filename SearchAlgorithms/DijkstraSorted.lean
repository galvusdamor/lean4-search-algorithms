import SearchAlgorithms.DijkstraFast
import SearchAlgorithms.AStarSorted

/-!
# Dijkstra with a maintained (sorted) search queue

`dijkstra_sorted` is `astar_sorted` with the zero heuristic, i.e. Dijkstra's algorithm running
on the search state of `SearchAlgorithms.HeuristicSearchSorted`: hash maps for the path order
and the mother relation, a hash-set backed visited set, and a queue that is kept sorted (with
a hash map of multiplicities for the queue-membership test).

Soundness, completeness and optimality come for free from `dijkstra`, via `dijkstra_sorted_eq`.
-/

namespace NatGraph

open WeightedDiGraph

variable {V : Type} [FinEnum V] [BEq V] [LawfulBEq V] [Hashable V]
variable (G : NatGraphWithGenerator V)

/-- Dijkstra's algorithm with a maintained sorted queue. -/
def dijkstra_sorted (start : V) (goal : V) : Option ((G.toWeightedDiGraph).Path start goal) :=
  astar_sorted G h_zero start goal

/-- `dijkstra_sorted` computes the same result as `dijkstra` on the underlying weighted
digraph. -/
theorem dijkstra_sorted_eq (start : V) (goal : V) :
    dijkstra_sorted G start goal = dijkstra (g := G.toWeightedDiGraph) start goal :=
  astar_sorted_eq G h_zero start goal

theorem dijkstra_sorted_is_sound (start : V) (goal : V) :
    (Option.isSome (dijkstra_sorted G start goal)
      → (∃ x : ((G.toWeightedDiGraph).Path start goal), x = x)) := by
  rw [dijkstra_sorted_eq]
  exact dijkstra_is_sound start goal

theorem dijkstra_sorted_is_complete (start : V) (goal : V) :
    ((∃ x : ((G.toWeightedDiGraph).Path start goal), x = x)
      → Option.isSome (dijkstra_sorted G start goal)) := by
  rw [dijkstra_sorted_eq]
  exact dijkstra_is_complete start goal

/-- Optimality of `dijkstra_sorted`: the returned path is a cheapest path to the goal. -/
theorem dijkstra_sorted_is_optimal (start : V) (goal : V)
    (returned_path : Option.isSome (dijkstra_sorted G start goal)) :
    ((dijkstra_sorted G start goal).get returned_path).is_cheapest := by
  simp only [dijkstra_sorted_eq] at returned_path ⊢
  exact dijkstra_is_optimal start goal returned_path

/-- `dijkstra_sorted` and `dijkstra_fast` return the same path. -/
theorem dijkstra_sorted_eq_fast (start : V) (goal : V) :
    dijkstra_sorted G start goal = dijkstra_fast G start goal := by
  rw [dijkstra_sorted_eq, dijkstra_fast_eq]

/-- `dijkstra_sorted` and `dijkstra_gen` return the same path. -/
theorem dijkstra_sorted_eq_gen (start : V) (goal : V) :
    dijkstra_sorted G start goal = dijkstra_gen G start goal := by
  rw [dijkstra_sorted_eq, dijkstra_gen_eq]

end NatGraph
