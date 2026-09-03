import SearchAlgorithms.AStarFast
import SearchAlgorithms.HeuristicSearchSorted

/-!
# A* with a maintained (sorted) search queue

`astar_sorted` is `astar_fast` (see `SearchAlgorithms.AStarFast`) running on the search state
of `SearchAlgorithms.HeuristicSearchSorted`: on top of the hash maps and the hash-set backed
visited set, the queue is *kept* sorted and comes with a hash map of multiplicities.  Hence

* the queue is not re-sorted after every expansion — the newly queued nodes are merged into
  it, and an expansion that queues nothing shares the old queue and costs `O(1)`;
* the test "is this neighbour still in the queue?" is a hash-map lookup instead of a scan.

Soundness, completeness and optimality are again obtained for free from the corresponding
results about `astar`, using

* `hsearch_step_expand_sorted_eq` — one expansion step produces the same **abstract** state
  whenever it is applied to the queue of its own state, and
* `WeightedDiGraph.search_exe_with_stack_step_sim_of_stack'` — a search whose state
  representation is changed in a way that preserves the abstract state (for the states the
  loop actually produces) returns the same result,

which together give
`astar_sorted G heur start goal = astar (g := G.toWeightedDiGraph) heur start goal`.
-/

namespace NatGraph

open WeightedDiGraph

variable {V : Type} [FinEnum V] [BEq V] [LawfulBEq V] [Hashable V]
variable (G : NatGraphWithGenerator V) (heur : V → ℕ∞)

/-- The termination metric on sorted states: the `nodeNum`-free metric of the abstract state
it encodes. -/
def hsearch_sorted_termination_metric (s : hsearch_sorted_state V heur) : ℕ × ℕ × ℕ × ℕ :=
  hsearch_termination_metric_nat (s.toBaseState (g := G.toWeightedDiGraph))

/-- The sorted expansion step decreases the termination metric. -/
theorem hsearch_sorted_expand_metric_reduction (goal : V) :
    WeightedDiGraph.termination_proof_for_expand (G := G.toWeightedDiGraph) (D := ℕ × ℕ)
      (state_type := hsearch_sorted_state V heur) (hsearch_step_expand_sorted G heur) goal
      (hsearch_sorted_termination_metric G heur) := by
  intro state head tail h
  have := hsearch_expand_metric_reduction_nat (g := G.toWeightedDiGraph) (goal := goal) heur
    (state.toBaseState (g := G.toWeightedDiGraph)) head tail h
  simpa only [hsearch_sorted_termination_metric,
    hsearch_step_expand_sorted_eq G heur state head tail h.2] using this

/-- The sorted expansion step preserves all basic search invariants. -/
theorem hsearch_sorted_expand_keeps_base_invars (start goal : V) :
    WeightedDiGraph.base_invar_carries_over_expand (G := G.toWeightedDiGraph) (D := ℕ × ℕ)
      (state_type := hsearch_sorted_state V heur) (hsearch_step_expand_sorted G heur) goal
      (WeightedDiGraph.search_invar_all_basic (G := G.toWeightedDiGraph) (D := ℕ × ℕ)
        (hsearch_expandable heur) start) := by
  intro s head tail h
  have hb := hsearch_step_expand_sorted_eq G heur s head tail h.2.2
  have hinv := hsearch_expand_keeps_base_invars (g := G.toWeightedDiGraph) (goal := goal)
    (start := start) heur (s.toBaseState (g := G.toWeightedDiGraph)) head tail h
  rw [show WeightedDiGraph.has_base_search_state.to_base_state
      (hsearch_step_expand_sorted G heur s head tail)
      = hsearch_step_expand (g := G.toWeightedDiGraph) heur
          (s.toBaseState (g := G.toWeightedDiGraph)) head tail from hb]
  exact hinv

/-- A* with a maintained sorted queue. -/
def astar_sorted (start : V) (goal : V) : Option ((G.toWeightedDiGraph).Path start goal) :=
  let start_state : hsearch_sorted_state V heur := hsearch_sorted_state.initial heur start ⟨0, 0⟩
  have h : WeightedDiGraph.has_base_search_state.to_base_state (G := G.toWeightedDiGraph)
      start_state = WeightedDiGraph.base_search_state_initial start (0, 0) :=
    hsearch_sorted_state.toBaseState_initial heur start (0, 0)
  WeightedDiGraph.search_exe_with_stack_step (G := G.toWeightedDiGraph) (start := start)
    (goal := goal) (start_state := start_state)
    (termination_metric := hsearch_sorted_termination_metric G heur)
    (hsearch_step_expand_sorted G heur)
    (hsearch_sorted_expand_metric_reduction G heur goal)
    (hsearch_sorted_expand_keeps_base_invars G heur start goal) h

/-- `astar_sorted` computes the same result as `astar` on the underlying weighted digraph. -/
theorem astar_sorted_eq (start : V) (goal : V) :
    astar_sorted G heur start goal = astar (g := G.toWeightedDiGraph) heur start goal := by
  unfold astar_sorted astar
  dsimp only
  -- Swap the reference metric for the cheap `nodeNum`-free one (the result does not depend
  -- on the metric).
  rw [search_exe_with_stack_step_metric_irrel
      (m := hsearch_termination_metric (g := G.toWeightedDiGraph))
      (m' := hsearch_termination_metric_nat (g := G.toWeightedDiGraph))
      (mp' := hsearch_expand_metric_reduction_nat heur)]
  -- Then change the state representation.
  have hsim := search_exe_with_stack_step_sim_of_stack' (G := G.toWeightedDiGraph) (D := ℕ × ℕ)
    (A := hsearch_sorted_state V heur) (B := hsearch_search_state G.toWeightedDiGraph)
    (fun s => s.toBaseState) (fun _ => rfl)
    (hsearch_step_expand_sorted G heur) (hsearch_step_expand heur)
    (fun s head tail hst => hsearch_step_expand_sorted_eq G heur s head tail hst)
    (hsearch_sorted_state.toBaseState_initial heur start (0, 0))
    (hsearch_sorted_termination_metric G heur) (hsearch_termination_metric_nat)
    (hsearch_sorted_expand_metric_reduction G heur goal)
    (hsearch_sorted_expand_keeps_base_invars G heur start goal)
    (hsearch_sorted_state.toBaseState_initial heur start (0, 0))
    (hsearch_expand_metric_reduction_nat heur) (hsearch_expand_keeps_base_invars heur) rfl
  exact hsim.symm

theorem astar_sorted_is_sound (start : V) (goal : V) :
    (Option.isSome (astar_sorted G heur start goal)
      → (∃ x : ((G.toWeightedDiGraph).Path start goal), x = x)) := by
  rw [astar_sorted_eq]
  exact astar_is_sound heur start goal

/-- Completeness of `astar_sorted`: identical hypothesis to `astar_is_complete` (a path all of
whose nodes have a finite heuristic value). -/
theorem astar_sorted_is_complete (start : V) (goal : V) :
    ((∃ p : ((G.toWeightedDiGraph).Path start goal), ∀ u ∈ p.support, hsearch_expandable heur u)
      → Option.isSome (astar_sorted G heur start goal)) := by
  rw [astar_sorted_eq]
  exact astar_is_complete heur start goal

/-- Optimality of `astar_sorted`: under an admissible heuristic the returned path is a
cheapest path to the goal. -/
theorem astar_sorted_is_optimal (start : V) (goal : V)
    (is_admissible : admissible (g := G.toWeightedDiGraph) heur goal)
    (returned_path : Option.isSome (astar_sorted G heur start goal)) :
    ((astar_sorted G heur start goal).get returned_path).is_cheapest := by
  simp only [astar_sorted_eq] at returned_path ⊢
  exact astar_is_optimal heur start goal is_admissible returned_path

/-- `astar_sorted` and `astar_fast` return the same path. -/
theorem astar_sorted_eq_fast (start : V) (goal : V) :
    astar_sorted G heur start goal = astar_fast G heur start goal := by
  rw [astar_sorted_eq, astar_fast_eq]

/-- `astar_sorted` and `astar_gen` return the same path. -/
theorem astar_sorted_eq_gen (start : V) (goal : V) :
    astar_sorted G heur start goal = astar_gen G heur start goal := by
  rw [astar_sorted_eq, astar_gen_eq]

end NatGraph
