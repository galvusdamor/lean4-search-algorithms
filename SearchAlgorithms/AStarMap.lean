import SearchAlgorithms.AStarGen
import SearchAlgorithms.HeuristicSearchMap

/-!
# A* on the flattened (hash-map) search state

`astar_map` is `astar_gen` (see `SearchAlgorithms.AStarGen`) running on the flattened search
state of `SearchAlgorithms.HeuristicSearchMap`: neighbours come from the generator, and the
path order and mother relation live in hash maps instead of in a chain of closures.

Soundness, completeness and optimality are obtained *for free* from the corresponding results
about `astar`, using

* `hsearch_step_expand_map_eq` — one expansion step produces the same **abstract** state, and
* `WeightedDiGraph.search_exe_with_stack_step_sim'` — a search whose state representation is
  changed in a way that preserves the abstract state returns the same result,

which together give `astar_map G heur start goal = astar (g := G.toWeightedDiGraph) heur start
goal`.
-/

namespace NatGraph

open WeightedDiGraph

variable {V : Type} [FinEnum V] [BEq V] [LawfulBEq V] [Hashable V]
variable (G : NatGraphWithGenerator V) (heur : V → ℕ∞)

/-- The termination metric on flattened states: the `nodeNum`-free metric of the abstract
state it encodes. -/
def hsearch_map_termination_metric (s : hsearch_map_state V) : ℕ × ℕ × ℕ × ℕ :=
  hsearch_termination_metric_nat (s.toBaseG G)

/-- The flattened expansion step decreases the termination metric. -/
theorem hsearch_map_expand_metric_reduction (goal : V) :
    WeightedDiGraph.termination_proof_for_expand (G := G.toWeightedDiGraph) (D := ℕ × ℕ)
      (state_type := hsearch_map_state V) (hsearch_step_expand_map G heur) goal
      (hsearch_map_termination_metric G) := by
  intro state head tail h
  have := hsearch_expand_metric_reduction_nat (g := G.toWeightedDiGraph) (goal := goal) heur
    (state.toBaseG G) head tail h
  simpa only [hsearch_map_termination_metric, hsearch_step_expand_map_eq] using this

/-- The flattened expansion step preserves all basic search invariants. -/
theorem hsearch_map_expand_keeps_base_invars (start goal : V) :
    WeightedDiGraph.base_invar_carries_over_expand (G := G.toWeightedDiGraph) (D := ℕ × ℕ)
      (state_type := hsearch_map_state V) (hsearch_step_expand_map G heur) goal
      (WeightedDiGraph.search_invar_all_basic (G := G.toWeightedDiGraph) (D := ℕ × ℕ)
        (hsearch_expandable heur) start) := by
  intro s head tail h
  have hb := hsearch_step_expand_map_eq G heur s head tail
  have hinv := hsearch_expand_keeps_base_invars (g := G.toWeightedDiGraph) (goal := goal)
    (start := start) heur (s.toBaseG G) head tail h
  rw [show WeightedDiGraph.has_base_search_state.to_base_state
      (hsearch_step_expand_map G heur s head tail)
      = hsearch_step_expand (g := G.toWeightedDiGraph) heur (s.toBaseG G) head tail from hb]
  exact hinv

/-- A* with the flattened, hash-map based search state. -/
def astar_map (start : V) (goal : V) : Option ((G.toWeightedDiGraph).Path start goal) :=
  let start_state : hsearch_map_state V := hsearch_map_state.initial start ⟨0, 0⟩
  have h : WeightedDiGraph.has_base_search_state.to_base_state (G := G.toWeightedDiGraph)
      start_state = WeightedDiGraph.base_search_state_initial start (0, 0) :=
    hsearch_map_state.toBaseState_initial start (0, 0)
  WeightedDiGraph.search_exe_with_stack_step (G := G.toWeightedDiGraph) (start := start)
    (goal := goal) (start_state := start_state)
    (termination_metric := hsearch_map_termination_metric G)
    (hsearch_step_expand_map G heur)
    (hsearch_map_expand_metric_reduction G heur goal)
    (hsearch_map_expand_keeps_base_invars G heur start goal) h

/-- `astar_map` computes the same result as `astar` on the underlying weighted digraph. -/
theorem astar_map_eq (start : V) (goal : V) :
    astar_map G heur start goal = astar (g := G.toWeightedDiGraph) heur start goal := by
  unfold astar_map astar
  dsimp only
  -- Swap the reference metric for the cheap `nodeNum`-free one (the result does not depend
  -- on the metric).
  rw [search_exe_with_stack_step_metric_irrel
      (m := hsearch_termination_metric (g := G.toWeightedDiGraph))
      (m' := hsearch_termination_metric_nat (g := G.toWeightedDiGraph))
      (mp' := hsearch_expand_metric_reduction_nat heur)]
  -- Then change the state representation.
  exact (search_exe_with_stack_step_sim' (G := G.toWeightedDiGraph) (D := ℕ × ℕ)
    (A := hsearch_map_state V) (B := hsearch_search_state G.toWeightedDiGraph)
    (fun s => s.toBaseG G) (fun _ => rfl)
    (hsearch_step_expand_map G heur) (hsearch_step_expand heur)
    (fun s head tail => hsearch_step_expand_map_eq G heur s head tail)
    (hsearch_map_state.toBaseState_initial start (0, 0))
    (hsearch_map_termination_metric G) (hsearch_termination_metric_nat)
    (hsearch_map_expand_metric_reduction G heur goal)
    (hsearch_map_expand_keeps_base_invars G heur start goal) _
    (hsearch_expand_metric_reduction_nat heur) (hsearch_expand_keeps_base_invars heur) _).symm

theorem astar_map_is_sound (start : V) (goal : V) :
    (Option.isSome (astar_map G heur start goal)
      → (∃ x : ((G.toWeightedDiGraph).Path start goal), x = x)) := by
  rw [astar_map_eq]
  exact astar_is_sound heur start goal

/-- Completeness of `astar_map`: identical hypothesis to `astar_is_complete` (a path all of
whose nodes have a finite heuristic value). -/
theorem astar_map_is_complete (start : V) (goal : V) :
    ((∃ p : ((G.toWeightedDiGraph).Path start goal), ∀ u ∈ p.support, hsearch_expandable heur u)
      → Option.isSome (astar_map G heur start goal)) := by
  rw [astar_map_eq]
  exact astar_is_complete heur start goal

/-- Optimality of `astar_map`: under an admissible heuristic the returned path is a cheapest
path to the goal. -/
theorem astar_map_is_optimal (start : V) (goal : V)
    (is_admissible : admissible (g := G.toWeightedDiGraph) heur goal)
    (returned_path : Option.isSome (astar_map G heur start goal)) :
    ((astar_map G heur start goal).get returned_path).is_cheapest := by
  simp only [astar_map_eq] at returned_path ⊢
  exact astar_is_optimal heur start goal is_admissible returned_path

/-- `astar_map` and `astar_gen` return the same path. -/
theorem astar_map_eq_gen (start : V) (goal : V) :
    astar_map G heur start goal = astar_gen G heur start goal := by
  rw [astar_map_eq, astar_gen_eq]

end NatGraph
