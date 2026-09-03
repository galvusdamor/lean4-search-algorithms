import SearchAlgorithms.AStarSorted
import SearchAlgorithms.HeuristicSearchHeap

/-!
# A* with a heap as search queue

`astar_heap` is `astar_sorted` (see `SearchAlgorithms.AStarSorted`) with the sorted *list*
replaced by the leftist heap of `SearchAlgorithms.HeuristicSearchHeap`:

* queueing a node costs `O(log m)` and shares the rest of the heap, instead of `O(m)` for the
  insertion into a sorted list;
* the next node to expand is the root of the heap, i.e. `O(1)`;
* the queue is never sorted during the search — the sorted list the correctness statements
  talk about is recovered from the heap only when the final state is inspected.

Because the abstract queue is not stored, the search runs with a step function of its own
(`hsearch_heap_step`, which pops the heap) through
`WeightedDiGraph.search_exe_with_step_eq`; `hsearch_heap_step_eq` proves that this is the
very same step as the one of the generic loop, so `search_exe_with_step_eq_stack` turns the
run into the ordinary `search_exe_with_stack_step` run.  From there soundness, completeness
and optimality are obtained exactly as for `astar_sorted`, from

* `hsearch_step_expand_heap_eq` — one expansion produces the same **abstract** state as the
  reference implementation whenever it is applied to the queue of its own state, and
* `WeightedDiGraph.search_exe_with_stack_step_sim_of_stack'`,

which together give
`astar_heap G heur start goal = astar (g := G.toWeightedDiGraph) heur start goal`.
-/

namespace NatGraph

open WeightedDiGraph
open SearchAlgorithms

variable {V : Type} [FinEnum V] [BEq V] [LawfulBEq V] [Hashable V]
variable (G : NatGraphWithGenerator V) (heur : V → ℕ∞)

/-- The termination metric on heap states: the `nodeNum`-free metric of the abstract state it
encodes. -/
def hsearch_heap_termination_metric (s : hsearch_heap_state V heur) : ℕ × ℕ × ℕ × ℕ :=
  hsearch_termination_metric_nat (s.toBaseState (g := G.toWeightedDiGraph))

/-- The heap expansion step decreases the termination metric. -/
theorem hsearch_heap_expand_metric_reduction (goal : V) :
    WeightedDiGraph.termination_proof_for_expand (G := G.toWeightedDiGraph) (D := ℕ × ℕ)
      (state_type := hsearch_heap_state V heur) (hsearch_step_expand_heap G heur) goal
      (hsearch_heap_termination_metric G heur) := by
  intro state head tail h
  have := hsearch_expand_metric_reduction_nat (g := G.toWeightedDiGraph) (goal := goal) heur
    (state.toBaseState (g := G.toWeightedDiGraph)) head tail h
  simpa only [hsearch_heap_termination_metric,
    hsearch_step_expand_heap_eq G heur state head tail h.2] using this

/-- The heap expansion step preserves all basic search invariants. -/
theorem hsearch_heap_expand_keeps_base_invars (start goal : V) :
    WeightedDiGraph.base_invar_carries_over_expand (G := G.toWeightedDiGraph) (D := ℕ × ℕ)
      (state_type := hsearch_heap_state V heur) (hsearch_step_expand_heap G heur) goal
      (WeightedDiGraph.search_invar_all_basic (G := G.toWeightedDiGraph) (D := ℕ × ℕ)
        (hsearch_expandable heur) start) := by
  intro s head tail h
  have hb := hsearch_step_expand_heap_eq G heur s head tail h.2.2
  have hinv := hsearch_expand_keeps_base_invars (g := G.toWeightedDiGraph) (goal := goal)
    (start := start) heur (s.toBaseState (g := G.toWeightedDiGraph)) head tail h
  rw [show WeightedDiGraph.has_base_search_state.to_base_state
      (hsearch_step_expand_heap G heur s head tail)
      = hsearch_step_expand (g := G.toWeightedDiGraph) heur
          (s.toBaseState (g := G.toWeightedDiGraph)) head tail from hb]
  exact hinv

/-- **A\* with a heap as search queue.**  The loop runs with `hsearch_heap_step`, which reads
the next node off the heap instead of off the (never built) sorted queue. -/
def astar_heap (start : V) (goal : V) : Option ((G.toWeightedDiGraph).Path start goal) :=
  let start_state : hsearch_heap_state V heur := hsearch_heap_state.initial heur start ⟨0, 0⟩
  have h : WeightedDiGraph.has_base_search_state.to_base_state (G := G.toWeightedDiGraph)
      start_state = WeightedDiGraph.base_search_state_initial start (0, 0) :=
    hsearch_heap_state.toBaseState_initial heur start (0, 0)
  WeightedDiGraph.search_exe_with_step_eq (G := G.toWeightedDiGraph) (start := start)
    (start_state := start_state)
    (termination_metric := hsearch_heap_termination_metric G heur)
    (hsearch_step_expand_heap G heur) goal
    (hsearch_heap_step G heur) (hsearch_heap_step_eq G heur)
    (hsearch_heap_expand_metric_reduction G heur goal)
    (hsearch_heap_expand_keeps_base_invars G heur start goal) h

/-- The heap search is the ordinary search loop: only the way the next node is found
differs. -/
theorem astar_heap_eq_stack (start : V) (goal : V) :
    astar_heap G heur start goal
      = WeightedDiGraph.search_exe_with_stack_step (G := G.toWeightedDiGraph) (start := start)
        (goal := goal) (start_state := hsearch_heap_state.initial heur start ⟨0, 0⟩)
        (termination_metric := hsearch_heap_termination_metric G heur)
        (hsearch_step_expand_heap G heur)
        (hsearch_heap_expand_metric_reduction G heur goal)
        (hsearch_heap_expand_keeps_base_invars G heur start goal)
        (hsearch_heap_state.toBaseState_initial heur start (0, 0)) :=
  WeightedDiGraph.search_exe_with_step_eq_stack (G := G.toWeightedDiGraph) (start := start)
    (start_state := hsearch_heap_state.initial heur start ⟨0, 0⟩)
    (termination_metric := hsearch_heap_termination_metric G heur)
    (hsearch_step_expand_heap G heur) goal
    (hsearch_heap_step G heur) (hsearch_heap_step_eq G heur)
    (hsearch_heap_expand_metric_reduction G heur goal)
    (hsearch_heap_expand_keeps_base_invars G heur start goal)
    (hsearch_heap_state.toBaseState_initial heur start (0, 0))

/-- **`astar_heap` computes the same result as `astar`** on the underlying weighted digraph. -/
theorem astar_heap_eq (start : V) (goal : V) :
    astar_heap G heur start goal = astar (g := G.toWeightedDiGraph) heur start goal := by
  rw [astar_heap_eq_stack]
  unfold astar
  dsimp only
  -- Swap the reference metric for the cheap `nodeNum`-free one (the result does not depend
  -- on the metric).
  rw [search_exe_with_stack_step_metric_irrel
      (m := hsearch_termination_metric (g := G.toWeightedDiGraph))
      (m' := hsearch_termination_metric_nat (g := G.toWeightedDiGraph))
      (mp' := hsearch_expand_metric_reduction_nat heur)]
  -- Then change the state representation.
  have hsim := search_exe_with_stack_step_sim_of_stack' (G := G.toWeightedDiGraph) (D := ℕ × ℕ)
    (A := hsearch_heap_state V heur) (B := hsearch_search_state G.toWeightedDiGraph)
    (fun s => s.toBaseState) (fun _ => rfl)
    (hsearch_step_expand_heap G heur) (hsearch_step_expand heur)
    (fun s head tail hst => hsearch_step_expand_heap_eq G heur s head tail hst)
    (hsearch_heap_state.toBaseState_initial heur start (0, 0))
    (hsearch_heap_termination_metric G heur) (hsearch_termination_metric_nat)
    (hsearch_heap_expand_metric_reduction G heur goal)
    (hsearch_heap_expand_keeps_base_invars G heur start goal)
    (hsearch_heap_state.toBaseState_initial heur start (0, 0))
    (hsearch_expand_metric_reduction_nat heur) (hsearch_expand_keeps_base_invars heur) rfl
  exact hsim.symm

theorem astar_heap_is_sound (start : V) (goal : V) :
    (Option.isSome (astar_heap G heur start goal)
      → (∃ x : ((G.toWeightedDiGraph).Path start goal), x = x)) := by
  rw [astar_heap_eq]
  exact astar_is_sound heur start goal

/-- Completeness of `astar_heap`: identical hypothesis to `astar_is_complete` (a path all of
whose nodes have a finite heuristic value). -/
theorem astar_heap_is_complete (start : V) (goal : V) :
    ((∃ p : ((G.toWeightedDiGraph).Path start goal), ∀ u ∈ p.support, hsearch_expandable heur u)
      → Option.isSome (astar_heap G heur start goal)) := by
  rw [astar_heap_eq]
  exact astar_is_complete heur start goal

/-- Optimality of `astar_heap`: under an admissible heuristic the returned path is a cheapest
path to the goal. -/
theorem astar_heap_is_optimal (start : V) (goal : V)
    (is_admissible : admissible (g := G.toWeightedDiGraph) heur goal)
    (returned_path : Option.isSome (astar_heap G heur start goal)) :
    ((astar_heap G heur start goal).get returned_path).is_cheapest := by
  simp only [astar_heap_eq] at returned_path ⊢
  exact astar_is_optimal heur start goal is_admissible returned_path

/-- `astar_heap` and `astar_sorted` return the same path. -/
theorem astar_heap_eq_sorted (start : V) (goal : V) :
    astar_heap G heur start goal = astar_sorted G heur start goal := by
  rw [astar_heap_eq, astar_sorted_eq]

/-- `astar_heap` and `astar_gen` return the same path. -/
theorem astar_heap_eq_gen (start : V) (goal : V) :
    astar_heap G heur start goal = astar_gen G heur start goal := by
  rw [astar_heap_eq, astar_gen_eq]

end NatGraph
