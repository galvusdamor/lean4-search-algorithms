import SearchAlgorithms.DijkstraHeap
import SearchAlgorithms.AStarHeapLazy

/-!
# Dijkstra with a lazily deleted heap as search queue

`dijkstra_heap_lazy` is `astar_heap_lazy` with the zero heuristic.  Dijkstra's relaxation is
exactly the decrease-key that the lazily deleted heap makes cheap, so this is the search that
profits most from `SearchAlgorithms.HeapLazyState`.

Soundness, completeness and optimality come for free from `dijkstra`, via
`dijkstra_heap_lazy_eq`.  `te` is the trace interval (`0` prints nothing); it defaults
to `100`.
-/

namespace NatGraph

open WeightedDiGraph

variable {V : Type} [FinEnum V] [BEq V] [LawfulBEq V] [Hashable V]
variable (G : NatGraphWithGenerator V)

/-- Dijkstra's algorithm with a lazily deleted heap as search queue. -/
def dijkstra_heap_lazy (start : V) (goal : V) (te : ℕ := 100) :
    Option ((G.toWeightedDiGraph).Path start goal) :=
  astar_heap_lazy G h_zero start goal te

/-- `dijkstra_heap_lazy` computes the same result as `dijkstra` on the underlying weighted
digraph. -/
theorem dijkstra_heap_lazy_eq (start : V) (goal : V) (te : ℕ) :
    dijkstra_heap_lazy G start goal te = dijkstra (g := G.toWeightedDiGraph) start goal :=
  astar_heap_lazy_eq G h_zero start goal te

theorem dijkstra_heap_lazy_is_sound (start : V) (goal : V) (te : ℕ) :
    (Option.isSome (dijkstra_heap_lazy G start goal te)
      → (∃ x : ((G.toWeightedDiGraph).Path start goal), x = x)) := by
  rw [dijkstra_heap_lazy_eq]
  exact dijkstra_is_sound start goal

theorem dijkstra_heap_lazy_is_complete (start : V) (goal : V) (te : ℕ) :
    ((∃ x : ((G.toWeightedDiGraph).Path start goal), x = x)
      → Option.isSome (dijkstra_heap_lazy G start goal te)) := by
  rw [dijkstra_heap_lazy_eq]
  exact dijkstra_is_complete start goal

/-- Optimality of `dijkstra_heap_lazy`: the returned path is a cheapest path to the goal. -/
theorem dijkstra_heap_lazy_is_optimal (start : V) (goal : V) (te : ℕ)
    (returned_path : Option.isSome (dijkstra_heap_lazy G start goal te)) :
    ((dijkstra_heap_lazy G start goal te).get returned_path).is_cheapest := by
  simp only [dijkstra_heap_lazy_eq] at returned_path ⊢
  exact dijkstra_is_optimal start goal returned_path

/-- `dijkstra_heap_lazy` and `dijkstra_heap` return the same path. -/
theorem dijkstra_heap_lazy_eq_heap (start : V) (goal : V) (te : ℕ) :
    dijkstra_heap_lazy G start goal te = dijkstra_heap G start goal := by
  rw [dijkstra_heap_lazy_eq, dijkstra_heap_eq]

/-- `dijkstra_heap_lazy` and `dijkstra_gen` return the same path. -/
theorem dijkstra_heap_lazy_eq_gen (start : V) (goal : V) (te : ℕ) :
    dijkstra_heap_lazy G start goal te = dijkstra_gen G start goal := by
  rw [dijkstra_heap_lazy_eq, dijkstra_gen_eq]

end NatGraph
