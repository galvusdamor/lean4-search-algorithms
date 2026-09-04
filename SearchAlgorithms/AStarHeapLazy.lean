import SearchAlgorithms.AStarHeap
import SearchAlgorithms.HeapLazyStep

/-!
# A* with a lazily deleted heap as search queue

`astar_heap_lazy` is `astar_heap` (see `SearchAlgorithms.AStarHeap`) with the eagerly updated
leftist heap replaced by the **lazily deleted** heap of
`SearchAlgorithms.HeapLazyState`:

* queueing a node costs `O(log m)`, as before;
* the next node to expand is the root of the heap, after dropping the stale entries in front
  of it — amortised `O(log m)`, since every entry is dropped at most once;
* a **decrease-key** costs `O(log m)` as well: the improved node is inserted again and its
  old entry is left in the heap as a stale entry.  This is the case `astar_heap` had to pay
  `Θ(m log m)` for, because there the comparison function reads the (changed) path order and
  the heap invariant may break.  Here every entry stores the path order it was queued with,
  so the comparison function never changes and the heap is never rebuilt.

Consequently *every* expansion costs `O(deg · log m)`, whatever the path orders do.

Correctness is not re-proved: `hsearch_step_expand_lazy_eq` says that one expansion produces
exactly the abstract state of the reference implementation, and everything transfers exactly
as for `astar_heap`, giving
`astar_heap_lazy G heur start goal te = astar (g := G.toWeightedDiGraph) heur start goal`.

## Instrumentation

The last argument `te` is the trace interval: every `te`-th expansion prints one progress
line on stderr (see `SearchAlgorithms.HeapLazyStep`); `te = 0` switches the output off.  It
defaults to `100`.  The output is produced by `dbg_trace`, which is the identity function, so
`te` does not influence the result — `astar_heap_lazy_eq` holds for every `te`.
-/

namespace NatGraph

open WeightedDiGraph
open SearchAlgorithms

variable {V : Type} [FinEnum V] [BEq V] [LawfulBEq V] [Hashable V]
variable (G : NatGraphWithGenerator V) (heur : V → ℕ∞)

/-- The termination metric on lazy heap states: the `nodeNum`-free metric of the abstract
state it encodes. -/
def hsearch_lazy_termination_metric (s : hsearch_lazy_state V heur) : ℕ × ℕ × ℕ × ℕ :=
  hsearch_termination_metric_nat (s.toBaseState (g := G.toWeightedDiGraph))

/-- The lazy heap expansion step decreases the termination metric. -/
theorem hsearch_lazy_expand_metric_reduction (goal : V) :
    WeightedDiGraph.termination_proof_for_expand (G := G.toWeightedDiGraph) (D := ℕ × ℕ)
      (state_type := hsearch_lazy_state V heur) (hsearch_step_expand_lazy G heur) goal
      (hsearch_lazy_termination_metric G heur) := by
  intro state head tail h
  have := hsearch_expand_metric_reduction_nat (g := G.toWeightedDiGraph) (goal := goal) heur
    (state.toBaseState (g := G.toWeightedDiGraph)) head tail h
  simpa only [hsearch_lazy_termination_metric,
    hsearch_step_expand_lazy_eq G heur state head tail h.2] using this

/-- The lazy heap expansion step preserves all basic search invariants. -/
theorem hsearch_lazy_expand_keeps_base_invars (start goal : V) :
    WeightedDiGraph.base_invar_carries_over_expand (G := G.toWeightedDiGraph) (D := ℕ × ℕ)
      (state_type := hsearch_lazy_state V heur) (hsearch_step_expand_lazy G heur) goal
      (WeightedDiGraph.search_invar_all_basic (G := G.toWeightedDiGraph) (D := ℕ × ℕ)
        (hsearch_expandable heur) start) := by
  intro s head tail h
  have hb := hsearch_step_expand_lazy_eq G heur s head tail h.2.2
  have hinv := hsearch_expand_keeps_base_invars (g := G.toWeightedDiGraph) (goal := goal)
    (start := start) heur (s.toBaseState (g := G.toWeightedDiGraph)) head tail h
  rw [show WeightedDiGraph.has_base_search_state.to_base_state
      (hsearch_step_expand_lazy G heur s head tail)
      = hsearch_step_expand (g := G.toWeightedDiGraph) heur
          (s.toBaseState (g := G.toWeightedDiGraph)) head tail from hb]
  exact hinv

/-- **A\* with a lazily deleted heap as search queue.**  The loop runs with
`hsearch_lazy_step`, which reads the next node off the heap instead of off the (never built)
sorted queue.  `te` is the trace interval (`0` prints nothing). -/
def astar_heap_lazy (start : V) (goal : V) (te : ℕ := 100) :
    Option ((G.toWeightedDiGraph).Path start goal) :=
  let start_state : hsearch_lazy_state V heur := hsearch_lazy_state.initial heur start ⟨0, 0⟩ te
  have h : WeightedDiGraph.has_base_search_state.to_base_state (G := G.toWeightedDiGraph)
      start_state = WeightedDiGraph.base_search_state_initial start (0, 0) :=
    hsearch_lazy_state.toBaseState_initial heur start (0, 0) te
  WeightedDiGraph.search_exe_with_step_eq (G := G.toWeightedDiGraph) (start := start)
    (start_state := start_state)
    (termination_metric := hsearch_lazy_termination_metric G heur)
    (hsearch_step_expand_lazy G heur) goal
    (hsearch_lazy_step G heur) (hsearch_lazy_step_eq G heur)
    (hsearch_lazy_expand_metric_reduction G heur goal)
    (hsearch_lazy_expand_keeps_base_invars G heur start goal) h

/-- The lazy heap search is the ordinary search loop: only the way the next node is found
differs. -/
theorem astar_heap_lazy_eq_stack (start : V) (goal : V) (te : ℕ) :
    astar_heap_lazy G heur start goal te
      = WeightedDiGraph.search_exe_with_stack_step (G := G.toWeightedDiGraph) (start := start)
        (goal := goal) (start_state := hsearch_lazy_state.initial heur start ⟨0, 0⟩ te)
        (termination_metric := hsearch_lazy_termination_metric G heur)
        (hsearch_step_expand_lazy G heur)
        (hsearch_lazy_expand_metric_reduction G heur goal)
        (hsearch_lazy_expand_keeps_base_invars G heur start goal)
        (hsearch_lazy_state.toBaseState_initial heur start (0, 0) te) :=
  WeightedDiGraph.search_exe_with_step_eq_stack (G := G.toWeightedDiGraph) (start := start)
    (start_state := hsearch_lazy_state.initial heur start ⟨0, 0⟩ te)
    (termination_metric := hsearch_lazy_termination_metric G heur)
    (hsearch_step_expand_lazy G heur) goal
    (hsearch_lazy_step G heur) (hsearch_lazy_step_eq G heur)
    (hsearch_lazy_expand_metric_reduction G heur goal)
    (hsearch_lazy_expand_keeps_base_invars G heur start goal)
    (hsearch_lazy_state.toBaseState_initial heur start (0, 0) te)

/-- **`astar_heap_lazy` computes the same result as `astar`** on the underlying weighted
digraph. -/
theorem astar_heap_lazy_eq (start : V) (goal : V) (te : ℕ) :
    astar_heap_lazy G heur start goal te = astar (g := G.toWeightedDiGraph) heur start goal := by
  rw [astar_heap_lazy_eq_stack]
  unfold astar
  dsimp only
  rw [search_exe_with_stack_step_metric_irrel
      (m := hsearch_termination_metric (g := G.toWeightedDiGraph))
      (m' := hsearch_termination_metric_nat (g := G.toWeightedDiGraph))
      (mp' := hsearch_expand_metric_reduction_nat heur)]
  have hsim := search_exe_with_stack_step_sim_of_stack' (G := G.toWeightedDiGraph) (D := ℕ × ℕ)
    (A := hsearch_lazy_state V heur) (B := hsearch_search_state G.toWeightedDiGraph)
    (fun s => s.toBaseState) (fun _ => rfl)
    (hsearch_step_expand_lazy G heur) (hsearch_step_expand heur)
    (fun s head tail hst => hsearch_step_expand_lazy_eq G heur s head tail hst)
    (hsearch_lazy_state.toBaseState_initial heur start (0, 0) te)
    (hsearch_lazy_termination_metric G heur) (hsearch_termination_metric_nat)
    (hsearch_lazy_expand_metric_reduction G heur goal)
    (hsearch_lazy_expand_keeps_base_invars G heur start goal)
    (hsearch_lazy_state.toBaseState_initial heur start (0, 0) te)
    (hsearch_expand_metric_reduction_nat heur) (hsearch_expand_keeps_base_invars heur) rfl
  exact hsim.symm

theorem astar_heap_lazy_is_sound (start : V) (goal : V) (te : ℕ) :
    (Option.isSome (astar_heap_lazy G heur start goal te)
      → (∃ x : ((G.toWeightedDiGraph).Path start goal), x = x)) := by
  rw [astar_heap_lazy_eq]
  exact astar_is_sound heur start goal

/-- Completeness of `astar_heap_lazy`: identical hypothesis to `astar_is_complete` (a path all
of whose nodes have a finite heuristic value). -/
theorem astar_heap_lazy_is_complete (start : V) (goal : V) (te : ℕ) :
    ((∃ p : ((G.toWeightedDiGraph).Path start goal), ∀ u ∈ p.support, hsearch_expandable heur u)
      → Option.isSome (astar_heap_lazy G heur start goal te)) := by
  rw [astar_heap_lazy_eq]
  exact astar_is_complete heur start goal

/-- Optimality of `astar_heap_lazy`: under an admissible heuristic the returned path is a
cheapest path to the goal. -/
theorem astar_heap_lazy_is_optimal (start : V) (goal : V) (te : ℕ)
    (is_admissible : admissible (g := G.toWeightedDiGraph) heur goal)
    (returned_path : Option.isSome (astar_heap_lazy G heur start goal te)) :
    ((astar_heap_lazy G heur start goal te).get returned_path).is_cheapest := by
  simp only [astar_heap_lazy_eq] at returned_path ⊢
  exact astar_is_optimal heur start goal is_admissible returned_path

/-- `astar_heap_lazy` and `astar_heap` return the same path. -/
theorem astar_heap_lazy_eq_heap (start : V) (goal : V) (te : ℕ) :
    astar_heap_lazy G heur start goal te = astar_heap G heur start goal := by
  rw [astar_heap_lazy_eq, astar_heap_eq]

/-- `astar_heap_lazy` and `astar_gen` return the same path. -/
theorem astar_heap_lazy_eq_gen (start : V) (goal : V) (te : ℕ) :
    astar_heap_lazy G heur start goal te = astar_gen G heur start goal := by
  rw [astar_heap_lazy_eq, astar_gen_eq]

end NatGraph
