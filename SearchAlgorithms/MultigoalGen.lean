import SearchAlgorithms.AStarGen
import SearchAlgorithms.DijkstraGen

/-!
# Generator-based multi-goal A* and Dijkstra (goal predicate)

This file combines the two earlier extensions of the heuristic search:

* the *generator*-based search (`astar_gen`/`dijkstra_gen`), which expands a node by
  iterating over its explicit neighbour list instead of enumerating the whole vertex set,
  and is therefore fast on very large graphs with short paths; and
* the *multi-goal* search driven by a **goal predicate** `is_goal : V → Prop`
  (`astar_multigoal_aux`), which reduces a search for *any* node satisfying `is_goal` to a
  single-goal search towards an artificial sink `none`.

The result is `astar_multigoal_gen` and `dijkstra_multigoal_gen`: multi-goal searches that
use the goal predicate *and* the neighbour generator, so they run on very large graphs with
short paths without ever materialising the whole vertex set.

The key construction is `add_artificial_goal_gen`: it augments a
`NatGraphWithGenerator` with the artificial sink `none`, providing a neighbour generator for
the augmented graph (`some u` gets an extra `none` neighbour exactly when `is_goal u`).  Its
underlying weighted digraph is *definitionally* the enumeration-based augmentation
`add_artificial_goal`, so running `astar_gen` on it computes the same result as the
enumeration-based multi-goal A*, and all soundness / completeness / optimality results
transfer via `astar_multigoal_gen_eq`.
-/

namespace NatGraph

open WeightedDiGraph

variable {V : Type} [FinEnum V]

-- Mathlib 4.31 made the standard subtype enumeration `implicit_reducible`.  Keep the
-- pre-4.31 concrete instance locally so the existing enumeration proofs remain unchanged.
local instance (priority := high) subtypeFinEnumCompat {α : Type} [FinEnum α]
    (p : α → Prop) [DecidablePred p] : FinEnum {x // p x} := FinEnum.subtypeCompat p
/-
The coerced enumeration of `↥(Finset.univ)` (as it appears in `neighbours_sublist`) is the
type-level `FinEnum` enumeration.
-/
theorem coe_toList_univ_eq (β : Type) [FinEnum β] :
    (FinEnum.toList (@Finset.univ β FinEnum.instFintype) : List β) = FinEnum.toList β := by
  simp only [FinEnum.toList]
  unfold subtypeFinEnumCompat FinEnum.subtypeCompat FinEnum.ofListCompat
    FinEnum.ofNodupListCompat
  simp +decide
  rw [List.dedup_eq_self.mpr]
  · rw [List.unattach, List.map_map]
    exact List.map_id'' (fun _ => rfl) _
  · exact List.Nodup.map
      (fun x y h => by simpa using congr_arg Subtype.val h) FinEnum.nodup_toList

/-
The type-level `FinEnum` enumeration of `Option V` lists `none` last: it is the
enumeration of `V` mapped through `some`, with `none` appended at the end.
-/
theorem toList_option_eq :
    FinEnum.toList (Option V) = (FinEnum.toList V).map some ++ [none] := by
  -- By definition of `FinEnum` for `Option V`, the list is the enumeration of `V` with `none` appended.
  simp only [FinEnum.toList]
  unfold instFinEnumOption_searchAlgorithms FinEnum.instFinEnumOptionLast FinEnum.insertNone
  have h_finRange_succ : List.finRange (FinEnum.card V + 1) = List.map (Fin.castSucc) (List.finRange (FinEnum.card V)) ++ [Fin.last (FinEnum.card V)] := by
    refine' List.ext_get _ _ <;> simp +decide
    grind +splitImp
  convert congr_arg ( fun l => List.map ( fun x => ( FinEnum.equiv.optionCongr.symm ( finSuccEquiv' ( Fin.last ( FinEnum.card V ) ) x ) ) ) l ) h_finRange_succ using 1
  simp +decide [ finSuccEquiv', Function.comp ]
  simp +decide [ Equiv.optionCongr ]

/-- The `FinEnum` enumeration of `Option V` lists `none` last: it is the enumeration of `V`
mapped through `some`, with `none` appended at the end. -/
theorem toList_univ_option_eq :
    (FinEnum.toList (@Finset.univ (Option V) FinEnum.instFintype) : List (Option V))
      = (FinEnum.toList (@Finset.univ V FinEnum.instFintype) : List V).map some ++ [none] := by
  rw [coe_toList_univ_eq (Option V), coe_toList_univ_eq V, toList_option_eq]

/-- Neighbour generator of the artificial-goal augmentation: `none` is a sink (no
out-neighbours), and `some u` keeps its original neighbours (through `some`), plus the
artificial sink `none` exactly when `is_goal u` holds. -/
def augNeighbours (G : NatGraphWithGenerator V) (is_goal : V → Prop) [DecidablePred is_goal] :
    Option V → List (Option V)
  | none => []
  | some u => (G.neighbours u).map some ++ (if is_goal u then [none] else [])

/-
`augNeighbours` is a correct adjacency generator for the augmented graph.
-/
theorem augNeighbours_are_adj (G : NatGraphWithGenerator V) (is_goal : V → Prop)
    [DecidablePred is_goal] (a b : Option V) :
    (add_artificial_goal G.toWeightedDiGraph is_goal).Adj a b ↔ b ∈ augNeighbours G is_goal a := by
  unfold add_artificial_goal;
  cases a <;> cases b <;> simp +decide [ G.neighbours_are_adj, augNeighbours ]

/-
Each `augNeighbours` list is an ordered sublist of the `FinEnum` enumeration of
`Option V`.
-/
theorem augNeighbours_sublist (G : NatGraphWithGenerator V) (is_goal : V → Prop)
    [DecidablePred is_goal] (a : Option V) :
    (augNeighbours G is_goal a).Sublist
      (FinEnum.toList (@Finset.univ (Option V) FinEnum.instFintype)) := by
  cases a with
  | none => exact List.nil_sublist _
  | some u =>
      rw [toList_univ_option_eq]
      unfold augNeighbours
      apply List.Sublist.append
      · exact List.Sublist.map some (G.neighbours_sublist u)
      · split_ifs
        · exact List.Sublist.refl [none]
        · exact List.nil_sublist [none]

/-- The artificial-goal augmentation of a *generator* graph for a goal predicate `is_goal`.

The underlying weighted digraph is exactly `add_artificial_goal` (so downstream results
transfer definitionally), and the neighbour generator adds, to the neighbours of `some u`,
the artificial sink `none` precisely when `is_goal u` holds. -/
def add_artificial_goal_gen (G : NatGraphWithGenerator V)
    (is_goal : V → Prop) [DecidablePred is_goal] : NatGraphWithGenerator (Option V) where
  toWeightedDiGraph := add_artificial_goal G.toWeightedDiGraph is_goal
  neighbours := augNeighbours G is_goal
  neighbours_are_adj := augNeighbours_are_adj G is_goal
  neighbours_sublist := augNeighbours_sublist G is_goal

/-- The underlying weighted digraph of the generator augmentation is the enumeration-based
augmentation. -/
@[simp] theorem add_artificial_goal_gen_toWeightedDiGraph (G : NatGraphWithGenerator V)
    (is_goal : V → Prop) [DecidablePred is_goal] :
    (add_artificial_goal_gen G is_goal).toWeightedDiGraph
      = add_artificial_goal G.toWeightedDiGraph is_goal := rfl

/-- Shared post-processing of the artificial-goal A* result.  Given the raw path from
`some start` to the artificial sink `none` in the augmented graph, drop the final artificial
edge and translate the result back to a path in the original graph, packaged with the (goal
predicate satisfying) real goal it reached.  Both the enumeration-based `astar_multigoal_aux`
and the generator-based `astar_multigoal_gen` are this post-processing applied to their
respective A* results. -/
def astar_multigoal_postprocess {g : NatGraph V} (start : V) (is_goal : V → Prop)
    [DecidablePred is_goal]
    (ret : Option ((g.add_artificial_goal is_goal).Path (some start) none)) :
    Option ((thegoal : {v : V // is_goal v}) × g.Path start thegoal) :=
  match ret with
  | none => none
  | some p => by
    obtain ⟨w, ⟨path, prop⟩⟩ := WeightedDiGraph.Path.snoc p (by simp)
    have w_is_some : w.isSome := by
      unfold Option.isSome
      unfold NatGraph.add_artificial_goal at prop
      simp at prop
      grind
    let w' : V := w.get w_is_some
    have w_is_goal : is_goal w' := by
      unfold NatGraph.add_artificial_goal at prop
      simp at prop
      grind
    have w_eq_some_w' : w = Option.some w' := by grind
    have pp : none ∉ (w_eq_some_w' ▸ path).support := by apply none_not_in_walk_to_some
    have p : g.Path start w' := NatGraph.translate_path (G := g) (w_eq_some_w' ▸ path) (pp)
    use Option.some ⟨⟨w', w_is_goal⟩, p⟩

/-
The enumeration-based multi-goal A* is exactly the shared post-processing applied to the
augmented-graph A* result.
-/
theorem astar_multigoal_aux_eq_postprocess {g : NatGraph V} (heur : V → ℕ∞) (start : V)
    (is_goal : V → Prop) [DecidablePred is_goal] :
    astar_multigoal_aux (g := g) heur start is_goal
      = astar_multigoal_postprocess start is_goal
          (astar (g := g.add_artificial_goal is_goal) (opt_heur heur) (some start) none) := by
  unfold astar_multigoal_aux;
  cases h : astar ( opt_heur heur ) ( some start ) none <;> simp_all +decide [ astar_multigoal_postprocess ]

/-! ### Generator-based multi-goal A* -/

/-- Multi-goal A* with a goal predicate, running on a generator graph.  Identical result to
`astar_multigoal_aux`, but the augmented graph is searched with the generator-based
`astar_gen`, so a node is expanded via its neighbour list rather than by enumerating all
vertices — making it fast on very large graphs with short paths. -/
def astar_multigoal_gen (G : NatGraphWithGenerator V) (heur : V → ℕ∞) (start : V)
    (is_goal : V → Prop) [DecidablePred is_goal] :
    Option ((thegoal : {v : V // is_goal v}) × (G.toWeightedDiGraph).Path start thegoal) :=
  dbg_trace "Starting 2 " ;
  astar_multigoal_postprocess (g := G.toWeightedDiGraph) start is_goal
    (astar_gen (add_artificial_goal_gen G is_goal) (opt_heur heur) (some start) none)

/-- `astar_multigoal_gen` computes the same result as the enumeration-based
`astar_multigoal_aux`. -/
theorem astar_multigoal_gen_eq (G : NatGraphWithGenerator V) (heur : V → ℕ∞) (start : V)
    (is_goal : V → Prop) [DecidablePred is_goal] :
    astar_multigoal_gen G heur start is_goal
      = astar_multigoal_aux (g := G.toWeightedDiGraph) heur start is_goal := by
  rw [astar_multigoal_aux_eq_postprocess]
  unfold astar_multigoal_gen
  rw [astar_gen_eq]
  rfl

theorem astar_multigoal_gen_is_sound (G : NatGraphWithGenerator V) (heur : V → ℕ∞) (start : V)
    (is_goal : V → Prop) [DecidablePred is_goal] :
    (Option.isSome (astar_multigoal_gen G heur start is_goal) →
      (∃ goal : V, is_goal goal ∧ ∃ x : (G.toWeightedDiGraph).Path start goal, x = x)) := by
  rw [astar_multigoal_gen_eq]
  exact astar_multigoal_aux_is_sound heur start is_goal

theorem astar_multigoal_gen_is_complete (G : NatGraphWithGenerator V) (heur : V → ℕ∞)
    (start : V) (is_goal : V → Prop) [DecidablePred is_goal] :
    ((∃ goal : V, is_goal goal ∧
        ∃ p : (G.toWeightedDiGraph).Path start goal, ∀ u ∈ p.support, heur u ≠ ⊤) →
      Option.isSome (astar_multigoal_gen G heur start is_goal)) := by
  rw [astar_multigoal_gen_eq]
  exact astar_multigoal_aux_is_complete heur start is_goal

/-- Optimality of generator-based multi-goal A*: under an admissible heuristic the returned
path is a cheapest path to its goal. -/
theorem astar_multigoal_gen_is_optimal (G : NatGraphWithGenerator V) (heur : V → ℕ∞)
    (start : V) (is_goal : V → Prop) [DecidablePred is_goal]
    (is_admissible : admissible_pred (g := G.toWeightedDiGraph) heur is_goal)
    (returned_path : Option.isSome (astar_multigoal_gen G heur start is_goal)) :
    ((astar_multigoal_gen G heur start is_goal).get returned_path).2.is_cheapest := by
  revert returned_path
  rw [astar_multigoal_gen_eq]
  exact astar_multigoal_aux_is_optimal heur start is_goal is_admissible

/-! ### Generator-based multi-goal Dijkstra

Dijkstra's algorithm is the special case of A* with the zero heuristic `h_zero`.  The
zero heuristic is finite everywhere, so completeness only needs a reachable goal, and it is
trivially admissible, so the returned path is always optimal. -/

/-- Multi-goal Dijkstra with a goal predicate, running on a generator graph. -/
def dijkstra_multigoal_gen (G : NatGraphWithGenerator V) (start : V)
    (is_goal : V → Prop) [DecidablePred is_goal] :
    Option ((thegoal : {v : V // is_goal v}) × (G.toWeightedDiGraph).Path start thegoal) :=
  astar_multigoal_gen G h_zero start is_goal

theorem dijkstra_multigoal_gen_is_sound (G : NatGraphWithGenerator V) (start : V)
    (is_goal : V → Prop) [DecidablePred is_goal] :
    (Option.isSome (dijkstra_multigoal_gen G start is_goal) →
      (∃ goal : V, is_goal goal ∧ ∃ x : (G.toWeightedDiGraph).Path start goal, x = x)) :=
  astar_multigoal_gen_is_sound G h_zero start is_goal

/-- Multi-goal Dijkstra is complete: if some node satisfying `is_goal` is reachable from
`start`, it finds a path.  (No finiteness side condition is needed: the zero heuristic is
finite everywhere.) -/
theorem dijkstra_multigoal_gen_is_complete (G : NatGraphWithGenerator V) (start : V)
    (is_goal : V → Prop) [DecidablePred is_goal] :
    ((∃ goal : V, is_goal goal ∧ ∃ p : (G.toWeightedDiGraph).Path start goal, p = p) →
      Option.isSome (dijkstra_multigoal_gen G start is_goal)) := by
  rintro ⟨goal, hgoal, p, -⟩
  exact astar_multigoal_gen_is_complete G h_zero start is_goal
    ⟨goal, hgoal, p, fun u _ => by simp only [h_zero]; exact WithTop.zero_ne_top⟩

/-- Multi-goal Dijkstra is optimal: the returned path is a cheapest path to its goal. -/
theorem dijkstra_multigoal_gen_is_optimal (G : NatGraphWithGenerator V) (start : V)
    (is_goal : V → Prop) [DecidablePred is_goal]
    (returned_path : Option.isSome (dijkstra_multigoal_gen G start is_goal)) :
    ((dijkstra_multigoal_gen G start is_goal).get returned_path).2.is_cheapest :=
  astar_multigoal_gen_is_optimal G h_zero start is_goal
    (fun _ _ _ _ => by simp only [h_zero]; exact zero_le) returned_path

end NatGraph
