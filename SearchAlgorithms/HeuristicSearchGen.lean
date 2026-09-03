import SearchAlgorithms.HeuristicSearch
import Mathlib.Tactic

/-!
# Generator-based heuristic search

This module provides a second version of the heuristic search of
`SearchAlgorithms.HeuristicSearch` that operates on a
`WeightedDiGraphWithGenerator`.  The only difference to the original
`hsearch_step_expand` is *how the neighbours of the current node are obtained*:

* the original algorithm enumerates **all** vertices of the graph
  (`FinEnum.toList Finset.univ`) and filters them by the adjacency relation;
* the generator-based algorithm iterates over the explicit neighbour list
  `G.neighbours stackHead` instead, and therefore never materialises the list of
  all vertices.

The main result, `hsearch_step_expand_gen_eq`, shows that a single expansion step
of the generator-based search produces **exactly** the same search state as the
enumeration-based search.  This equivalence is then used to transfer soundness,
completeness and optimality from the original algorithm to the generator-based
one (see `SearchAlgorithms.AStarGen` and `SearchAlgorithms.DijkstraGen`).
-/

namespace NatGraph

open WeightedDiGraph

variable {V : Type} [FinEnum V]

/-- A `NatGraph` (ℕ-weighted digraph) equipped with an adjacency generator. -/
abbrev NatGraphWithGenerator (V : Type) [FinEnum V] := WeightedDiGraphWithGenerator V ℕ

/-!
## Auxiliary lemmas
-/

/-
If `s` is a sublist of the duplicate-free list `l` and every element of `l`
that satisfies `p` already occurs in `s`, then filtering `l` by `p` gives the same
list as filtering `s` by `p`.  (Both `filter`s keep the elements in their original
`l`-order, and by the hypotheses they select exactly the same elements.)
-/
theorem filter_eq_of_sublist_of_mem {α : Type} (p : α → Bool) {s l : List α}
    (hsub : s.Sublist l) (hnodup : l.Nodup) (hmem : ∀ x ∈ l, p x → x ∈ s) :
    l.filter p = s.filter p := by
  induction' hsub with a b hsub ih
  · rfl
  · grind
  · grind

/-- `filterMap`-ing an `attach`ed list with a predicate whose `some`/`none` choice does not
depend on the membership proof is the same as `filter`ing the underlying list. -/
theorem attach_filterMap_if_eq_filter {α : Type} (l : List α) (p : α → Bool) :
    l.attach.filterMap (fun x => if p x.1 then some x.1 else none) = l.filter p := by
  induction l with
  | nil => simp
  | cons a t ih =>
    simp only [List.attach_cons, List.filterMap_cons, List.filterMap_map, List.filter_cons,
      Function.comp_def, ih]
    by_cases h : p a <;> simp [h]

/-- Dependent variant of `attach_filterMap_if_eq_filter`: if the (membership-dependent)
decision predicate `q` agrees with a plain boolean predicate `p` on every element, then
`filterMap`-ing the `attach`ed list by `q` equals `filter`ing by `p`. -/
theorem attach_filterMap_dite_eq_filter {α : Type} (l : List α) (q : (v : α) → v ∈ l → Prop)
    [∀ v h, Decidable (q v h)]
    (p : α → Bool) (hq : ∀ v (h : v ∈ l), decide (q v h) = p v) :
    l.attach.filterMap (fun x => if q x.1 x.2 then some x.1 else none) = l.filter p := by
  rw [← attach_filterMap_if_eq_filter l p]
  apply List.filterMap_congr
  intro x hx
  have hx2 := hq x.1 x.2
  rw [← hx2]
  simp

/-- Congruence lemma for `base_search_state`: two search states are equal as soon as
their `visited` sets, their `pathOrder` functions, their `stack`s agree and their
`mother` functions agree pointwise.  Stated with `visited` as universally quantified
variables so that the (dependent) `mother` field can be handled by `subst`. -/
theorem base_search_state_congr {E : Type} {G : WeightedDiGraph V E}
    {D : Type} [FValueComp D]
    {v1 v2 : Finset V} (hv : v1 = v2) {o1 o2 : V → D} (ho : o1 = o2)
    {m1 : v1 → V} {m2 : v2 → V}
    (hm : ∀ (x : V) (h1 : x ∈ v1) (h2 : x ∈ v2), m1 ⟨x, h1⟩ = m2 ⟨x, h2⟩)
    {s1 s2 : List V} (hs : s1 = s2) :
    (⟨v1, o1, m1, s1⟩ : base_search_state G D) = ⟨v2, o2, m2, s2⟩ := by
  subst hv; subst ho; subst hs
  have : m1 = m2 := by
    funext x
    obtain ⟨x, hx⟩ := x
    exact hm x hx hx
  subst this
  rfl

/-- The neighbour list of any vertex is duplicate-free: it is a sublist of the (duplicate-free)
`FinEnum` enumeration of all vertices. -/
theorem neighbours_nodup {E : Type} (G : WeightedDiGraphWithGenerator V E) (u : V) :
    (G.neighbours u).Nodup := by
  apply (G.neighbours_sublist u).nodup
  simp only [bind_pure_comp]
  exact FinEnum.nodup_toList.map (fun a b hab => Subtype.ext hab)

/-!
## The generator-based expansion step
-/

/-- One expansion step of the generator-based heuristic search.

This mirrors `hsearch_step_expand` exactly, except that the set of newly-visited
neighbours is obtained by iterating over `G.neighbours stackHead` instead of
enumerating all vertices of the graph. -/
def hsearch_step_expand_gen
    (G : NatGraphWithGenerator V)
    (heur : V → ℕ∞)
    (priorState : hsearch_search_state G.toWeightedDiGraph)
    (stackHead : V)
    (stackTail : List V) :
    hsearch_search_state G.toWeightedDiGraph :=
  dbg_trace "Expand stack size is {stackTail.length} {priorState.visited.card}" ; 
  let g : NatGraph V := G.toWeightedDiGraph
  -- The newly-visited neighbours.  Because we iterate over `G.neighbours stackHead`,
  -- every candidate is *known* to be adjacent to `stackHead` — the required adjacency
  -- proof is obtained from list membership via `neighbours_are_adj` (no `G.Adj`
  -- decision is performed).
  let newly_visited_list : List V := (G.neighbours stackHead).attach.filterMap
    (fun ⟨v, hv⟩ =>
      let adj : g.Adj stackHead v := (G.neighbours_are_adj stackHead v).mpr hv
      if heur v ≠ ⊤ ∧ (v ∉ priorState.visited ∨
        (v ∈ priorState.visited ∧ v ∉ stackTail ∧
          (priorState.pathOrder v).fst > (priorState.pathOrder stackHead).fst + g.edgeCost adj)) then some v else none)
  let newly_visited : Finset V := newly_visited_list.toFinset
  let new_visited : Finset V := priorState.visited ∪ newly_visited

  let new_order : V → ℕ × ℕ := fun v  =>
    if h : @decide (g.Adj stackHead v) (g.instDecAdj stackHead v) then
      let adj : g.Adj stackHead v := by simp_all only [decide_eq_true_eq]
      if (v ∉ priorState.visited) then path_val priorState stackHead v adj
      else new_cost priorState stackHead v adj
    else priorState.pathOrder v

  let new_mother : new_visited → V := fun ⟨v, hv⟩  =>
    if not_visited_before : (v ∉ priorState.visited) then
      stackHead
    else
      if priorState.pathOrder v = new_order v then
        priorState.mother ⟨v, by simp_all⟩
      else
        stackHead

  let new_stack : List V := (stackTail ++ newly_visited_list).mergeSort (fun a b =>
     add_heur a (new_order a) heur = add_heur b (new_order b) heur || FValueComp.lt (add_heur a (new_order a) heur) (add_heur b (new_order b) heur))

  WeightedDiGraph.base_search_state.mk new_visited new_order new_mother new_stack

/-- Extensionality for `base_search_state` via projections: two states are equal if
their `visited`, `pathOrder`, `stack` fields agree and their `mother` functions agree
pointwise. -/
theorem base_search_state_eq {E : Type} {G : WeightedDiGraph V E}
    {D : Type} [FValueComp D] (s1 s2 : base_search_state G D)
    (hv : s1.visited = s2.visited) (ho : s1.pathOrder = s2.pathOrder)
    (hm : ∀ (x : V) (h1 : x ∈ s1.visited) (h2 : x ∈ s2.visited),
      s1.mother ⟨x, h1⟩ = s2.mother ⟨x, h2⟩)
    (hs : s1.stack = s2.stack) : s1 = s2 := by
  obtain ⟨v1, o1, m1, st1⟩ := s1
  obtain ⟨v2, o2, m2, st2⟩ := s2
  exact base_search_state_congr hv ho hm hs

/-- The executable stack-based search depends on its expansion function only: replacing
the expansion function by an equal one (with any transported proof obligations) yields the
same result.  This holds because the proof obligations are propositions and hence
irrelevant. -/
theorem search_exe_with_stack_step_congr {E : Type}
    {G : WeightedDiGraph V E}
    {D : Type} [FValueComp D] {T : Type} [WellFoundedRelation T]
    {state_type : Type} [G.has_base_search_state D state_type]
    {start : V} {expandable : V → Prop} {d : D}
    {start_state : state_type} {goal : V} {termination_metric : state_type → T}
    {e1 e2 : search_expand G D (state_type := state_type)}
    (he : e1 = e2)
    (m1 : termination_proof_for_expand e1 goal termination_metric)
    (i1 : base_invar_carries_over_expand e1 goal (search_invar_all_basic expandable start))
    (h1 : (has_base_search_state.to_base_state (G:=G) (D:=D) start_state)
      = (base_search_state_initial start d))
    (m2 : termination_proof_for_expand e2 goal termination_metric)
    (i2 : base_invar_carries_over_expand e2 goal (search_invar_all_basic expandable start))
    (h2 : (has_base_search_state.to_base_state (G:=G) (D:=D) start_state)
      = (base_search_state_initial start d)) :
    search_exe_with_stack_step (start:=start) (d:=d) (expandable:=expandable) (goal:=goal)
        (start_state:=start_state) (termination_metric:=termination_metric) e1 m1 i1 h1
      = search_exe_with_stack_step (start:=start) (d:=d) (expandable:=expandable) (goal:=goal)
        (start_state:=start_state) (termination_metric:=termination_metric) e2 m2 i2 h2 := by
  subst he; rfl

/-!
## Equivalence of one expansion step, field by field
-/

/-- The `pathOrder` field agrees with the enumeration-based step.  The generator-based step
stores exactly the same per-vertex distance function `new_order` as `hsearch_step_expand`
(the two differ only in *how the neighbour frontier is enumerated*, not in the distances they
record), so this holds definitionally. -/
theorem hsearch_gen_pathOrder
    (G : NatGraphWithGenerator V) (heur : V → ℕ∞)
    (priorState : hsearch_search_state G.toWeightedDiGraph)
    (stackHead : V) (stackTail : List V) :
    (hsearch_step_expand_gen G heur priorState stackHead stackTail).pathOrder
      = (hsearch_step_expand (g := G.toWeightedDiGraph) heur priorState stackHead stackTail).pathOrder := by
  rfl

/-
The set of newly-visited vertices computed from the neighbour list agrees with the
one computed by enumerating and filtering all vertices.
-/
theorem hsearch_gen_visited
    (G : NatGraphWithGenerator V) (heur : V → ℕ∞)
    (priorState : hsearch_search_state G.toWeightedDiGraph)
    (stackHead : V) (stackTail : List V) :
    (hsearch_step_expand_gen G heur priorState stackHead stackTail).visited
      = (hsearch_step_expand (g := G.toWeightedDiGraph) heur priorState stackHead stackTail).visited := by
  refine' congr_arg₂ ( · ∪ · ) rfl ( Finset.ext fun x => _ );
  simp +decide [ Finset.mem_filterMap, List.mem_toFinset, G.neighbours_are_adj ]

/-
The queue produced by the generator-based step equals the one produced by the
enumeration-based step: both `mergeSort` `stackTail ++ newly_visited_list` with the same
comparator, and the two `newly_visited_list`s are equal.
-/
theorem hsearch_gen_stack
    (G : NatGraphWithGenerator V) (heur : V → ℕ∞)
    (priorState : hsearch_search_state G.toWeightedDiGraph)
    (stackHead : V) (stackTail : List V) :
    (hsearch_step_expand_gen G heur priorState stackHead stackTail).stack
      = (hsearch_step_expand (g := G.toWeightedDiGraph) heur priorState stackHead stackTail).stack := by
  refine congr_arg (fun l => List.mergeSort (stackTail ++ l) _) ?_
  letI : DecidableRel (G.toWeightedDiGraph).Adj := G.instDecAdj
  -- A self-contained boolean predicate: "adjacent to `stackHead` and expandable".
  set P : V → Bool := fun v =>
    if h : (G.toWeightedDiGraph).Adj stackHead v then
      decide (heur v ≠ ⊤ ∧ (v ∉ priorState.visited ∨
        (v ∈ priorState.visited ∧ v ∉ stackTail ∧
          (priorState.pathOrder v).fst > (priorState.pathOrder stackHead).fst
            + NatGraph.edgeCost h)))
    else false with hP
  -- Step 1: the generator list equals `filter P` over the neighbour list.
  have h1 : (G.neighbours stackHead).attach.filterMap
      (fun x => if heur x.1 ≠ ⊤ ∧ (x.1 ∉ priorState.visited ∨
          (x.1 ∈ priorState.visited ∧ x.1 ∉ stackTail ∧
            (priorState.pathOrder x.1).fst > (priorState.pathOrder stackHead).fst
              + NatGraph.edgeCost ((G.neighbours_are_adj stackHead x.1).mpr x.2)))
        then some x.1 else none)
      = (G.neighbours stackHead).filter P := by
    refine attach_filterMap_dite_eq_filter (G.neighbours stackHead)
      (fun v hv => heur v ≠ ⊤ ∧ (v ∉ priorState.visited ∨
        (v ∈ priorState.visited ∧ v ∉ stackTail ∧
          (priorState.pathOrder v).fst > (priorState.pathOrder stackHead).fst
            + NatGraph.edgeCost ((G.neighbours_are_adj stackHead v).mpr hv)))) P ?_
    intro v hv
    have hadj : (G.toWeightedDiGraph).Adj stackHead v := (G.neighbours_are_adj stackHead v).mpr hv
    simp only [hP, dif_pos hadj]
  rw [h1]
  -- Step 2: transfer the `filter P` from the neighbour list to the full enumeration
  -- (which is a super-list), matching the enumeration-based `filterMap`.
  rw [← filter_eq_of_sublist_of_mem]
  convert rfl
  · ext; simp +decide [hP, Finset.mem_filterMap]
    congr! 2
    change List.filterMap _ (FinEnum.toList (Finset.univ : Finset V)).unattach =
      List.filter _ (FinEnum.toList (Finset.univ : Finset V)).unattach
    generalize (FinEnum.toList (Finset.univ : Finset V)).unattach = enum
    induction enum <;> simp +decide [*, List.filterMap_cons]
    split_ifs <;> simp +decide [*]
  · have hunattach : (FinEnum.toList (Finset.univ : Finset V)).unattach = (do
        let a ← FinEnum.toList (Finset.univ : Finset V)
        pure a.1) := by
      unfold List.unattach
      change List.map (fun a : {v : V // v ∈ (Finset.univ : Finset V)} => a.1) _ =
        List.flatMap (fun a : {v : V // v ∈ (Finset.univ : Finset V)} => [a.1]) _
      exact List.map_eq_flatMap
    rw [hunattach]
    exact G.neighbours_sublist stackHead
  · exact List.Nodup.map Subtype.val_injective FinEnum.nodup_toList
  · intro v _ hPv
    simp only [hP] at hPv
    by_cases hadj : (G.toWeightedDiGraph).Adj stackHead v
    · exact (G.neighbours_are_adj stackHead v).mp hadj
    · simp [hadj] at hPv

/--
The `mother` functions agree pointwise.
-/
theorem hsearch_gen_mother
    (G : NatGraphWithGenerator V) (heur : V → ℕ∞)
    (priorState : hsearch_search_state G.toWeightedDiGraph)
    (stackHead : V) (stackTail : List V) (x : V)
    (h1 : x ∈ (hsearch_step_expand_gen G heur priorState stackHead stackTail).visited)
    (h2 : x ∈ (hsearch_step_expand (g := G.toWeightedDiGraph) heur priorState stackHead stackTail).visited) :
    (hsearch_step_expand_gen G heur priorState stackHead stackTail).mother ⟨x, h1⟩
      = (hsearch_step_expand (g := G.toWeightedDiGraph) heur priorState stackHead stackTail).mother ⟨x, h2⟩ := by
  -- Both `mother` functions are the *same* term: the (proof-irrelevant) membership proof is
  -- the only difference, and the `dbg_trace` in the generator step unfolds definitionally.
  rfl

/-!
## Equivalence of one expansion step
-/

/-- A single generator-based expansion step produces exactly the same search state
as the enumeration-based `hsearch_step_expand`. -/
theorem hsearch_step_expand_gen_eq
    (G : NatGraphWithGenerator V) (heur : V → ℕ∞)
    (priorState : hsearch_search_state G.toWeightedDiGraph)
    (stackHead : V) (stackTail : List V) :
    hsearch_step_expand_gen G heur priorState stackHead stackTail
      = hsearch_step_expand (g := G.toWeightedDiGraph) heur priorState stackHead stackTail :=
  base_search_state_eq _ _
    (hsearch_gen_visited G heur priorState stackHead stackTail)
    (hsearch_gen_pathOrder G heur priorState stackHead stackTail)
    (hsearch_gen_mother G heur priorState stackHead stackTail)
    (hsearch_gen_stack G heur priorState stackHead stackTail)

/-- The generator-based expansion step, viewed as a `search_expand` on the underlying
weighted digraph, is equal to the enumeration-based one. -/
theorem hsearch_step_expand_gen_eq_fun
    (G : NatGraphWithGenerator V) (heur : V → ℕ∞) :
    hsearch_step_expand_gen G heur
      = hsearch_step_expand (g := G.toWeightedDiGraph) heur := by
  funext priorState stackHead stackTail
  exact hsearch_step_expand_gen_eq G heur priorState stackHead stackTail

end NatGraph
