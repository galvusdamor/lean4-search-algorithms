import SearchAlgorithms.DijkstraAllNodes
import SearchAlgorithms.ExtractPathFast

/-!
# Shortest paths to all nodes with linear-time path reconstruction

`NatGraph.dijkstra_all_extract_path` reads a shortest path to a single node off the exhausted
search state of `SearchAlgorithms.DijkstraAllNodes` with
`WeightedDiGraph.extract_path_to`, which is `Θ(L²)` in the length `L` of that path.  Since one
usually extracts a path for *many* nodes from the same state, this is the place where the
quadratic reconstruction hurts most.

`dijkstra_all_extract_path_fast` does the same with the linear reconstruction of
`SearchAlgorithms.ExtractPathFast`, and `dijkstra_all_extract_path_fast_eq` proves that it
returns literally the same option, so `dijkstra_all_extract_path_eq_none_iff` and
`dijkstra_all_extract_path_spec` (cheapest path, cost = computed distance) hold for it
verbatim.
-/

variable {V : Type} [FinEnum V] [DecidableEq V]
variable {g : NatGraph V}

namespace NatGraph

open WeightedDiGraph

omit [DecidableEq V] in
/-- Translating equal augmented paths gives equal paths (the second argument is a proof and
hence irrelevant). -/
theorem translate_path_congr {a b : V} {is_goal : V → Prop} [DecidablePred is_goal]
    {p q : (g.add_artificial_goal is_goal).Path (some a) (some b)} (hpq : p = q)
    (hp : Option.none ∉ p.support) (hq : Option.none ∉ q.support) :
    translate_path p hp = translate_path q hq := by
  subst hpq
  rfl

/-- **A shortest path to `v`, reconstructed in linear time** from the exhausted search state
of the all-nodes Dijkstra. -/
def dijkstra_all_extract_path_fast (start v : V) : Option (g.Path start v) :=
  if hv : (some v) ∈ (dijkstra_all_final_state (g:=g) start).visited then
    let fs := dijkstra_all_final_state (g:=g) start
    let basic := (dijkstra_all_final_state_full_invar (g:=g) start).1
    let aug := extract_path_fast (some start) (some v) fs hv basic.2.1 basic.2.2.1 basic.2.2.2.1
    some (translate_path aug (none_not_in_walk_to_some aug.val))
  else
    none

/-- **The fast extraction returns the same option as `dijkstra_all_extract_path`.** -/
theorem dijkstra_all_extract_path_fast_eq (start v : V) :
    dijkstra_all_extract_path_fast (g:=g) start v = dijkstra_all_extract_path (g:=g) start v := by
  unfold dijkstra_all_extract_path_fast dijkstra_all_extract_path
  by_cases hv : (some v) ∈ (dijkstra_all_final_state (g:=g) start).visited
  · rw [dif_pos hv, dif_pos hv]
    exact congrArg some (translate_path_congr (extract_path_fast_eq _ _ _ _ _ _ _) _ _)
  · rw [dif_neg hv, dif_neg hv]

/-- The fast extraction returns `none` exactly for unreachable nodes. -/
theorem dijkstra_all_extract_path_fast_eq_none_iff (start v : V) :
    dijkstra_all_extract_path_fast (g:=g) start v = none ↔ ¬ Nonempty (g.Path start v) := by
  rw [dijkstra_all_extract_path_fast_eq]
  exact dijkstra_all_extract_path_eq_none_iff start v

/-- For reachable nodes the fast extraction returns a cheapest path whose cost is exactly the
computed distance. -/
theorem dijkstra_all_extract_path_fast_spec (start v : V) (p : g.Path start v) :
    ∃ q : g.Path start v,
      dijkstra_all_extract_path_fast (g:=g) start v = some q
        ∧ q.is_cheapest
        ∧ (q.cost : ℕ∞) = dijkstra_all_dist (g:=g) start v := by
  rw [dijkstra_all_extract_path_fast_eq]
  exact dijkstra_all_extract_path_spec start v p

end NatGraph
