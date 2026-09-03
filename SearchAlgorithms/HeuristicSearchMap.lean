import SearchAlgorithms.HeuristicSearchGen
import SearchAlgorithms.SearchSim

/-!
# Heuristic search with a *flattened* (hash-map based) search state

The reference search state `WeightedDiGraph.base_search_state` stores

* `pathOrder : V → D`   — a **function**, and
* `mother   : visited → V` — again a **function**.

Every expansion step of `hsearch_step_expand` (and of its generator-based variant
`hsearch_step_expand_gen`) builds the new `pathOrder`/`mother` as a *closure around the
previous one*:

```
new_order = fun v => if adj stackHead v then … else priorState.pathOrder v
```

After `k` expansions a single lookup therefore walks through a chain of `k` closures, each
of which performs an adjacency decision and a `Finset` membership test.  The cost of one
expansion grows with the number of steps already performed — and each expansion performs
many lookups (the queue comparator alone evaluates the order of every queued node), so a
search slows down dramatically after a few dozen expansions, even on a small graph.

This module provides a third implementation, `hsearch_step_expand_map`, whose state
(`hsearch_map_state`) keeps the same information in *flattened* form:

* `orderMap  : Std.HashMap V (ℕ × ℕ)` with a default value `orderDefault`, and
* `motherMap : Std.HashMap V V` with a default value `motherDefault`.

A lookup is a single hash-map access, independent of the number of steps performed, and one
expansion inserts one entry per neighbour of the expanded node.

## Correctness

Nothing is re-proved.  `hsearch_map_state` becomes a
`WeightedDiGraph.has_base_search_state` through the abstraction function `toBaseState`, and
the theorem

```
hsearch_step_expand_map_eq :
  (hsearch_step_expand_map G heur s head tail).toBaseState
    = hsearch_step_expand heur s.toBaseState head tail
```

states that *after every expansion the abstract search state is the same*, no matter how it
is encoded.  Together with the generic transfer theorem
`WeightedDiGraph.search_exe_with_stack_step_sim` (see `SearchAlgorithms.SearchSim`) this
yields that the whole search returns literally the same path (see
`SearchAlgorithms.AStarMap`), so soundness, completeness and optimality carry over verbatim.

The vertex type needs `[BEq V] [LawfulBEq V] [Hashable V]` for the hash maps; the ambient
`Finset` operations keep using the `DecidableEq` instance coming from `FinEnum`, exactly as
in `SearchAlgorithms.HeuristicSearchGen`.
-/

namespace NatGraph

open WeightedDiGraph

variable {V : Type} [FinEnum V] [BEq V] [LawfulBEq V] [Hashable V]

/-!
## A hash-map lemma
-/

/-- Value of `a` after inserting a whole list into a hash map, where the key of a list
element `x` is `key x` and its value is `val x`.  If the inserted values only depend on the
key (`hval`), the result is `f a` for every key occurring in the list, and the old value for
every other key. -/
theorem getD_foldl_insert {β γ : Type} (l : List γ) (key : γ → V) (val : γ → β)
    (f : V → β) (hval : ∀ x ∈ l, val x = f (key x))
    (m : Std.HashMap V β) (a : V) (dflt : β) :
    (l.foldl (fun m x => m.insert (key x) (val x)) m).getD a dflt
      = if a ∈ l.map key then f a else m.getD a dflt := by
  induction l generalizing m with
  | nil => simp
  | cons b t ih =>
    rw [List.foldl_cons, ih (fun x hx => hval x (List.mem_cons_of_mem b hx))]
    simp only [List.map_cons, List.mem_cons]
    by_cases hmem : a ∈ t.map key
    · simp [hmem]
    · by_cases hab : a = key b
      · subst hab
        simp [hmem, hval b (List.mem_cons_self ..)]
      · simp [hmem, hab, Std.HashMap.getD_insert, Ne.symm hab]

/-!
## The flattened search state
-/

/-- A heuristic-search state that stores the path order and the mother relation in hash
maps instead of closures.

`orderDefault` is the value returned for vertices that have not been touched yet (the
constant `d` of `base_search_state_initial`); `motherDefault` plays the same role for the
mother relation — its value is irrelevant, as `mother` is only ever queried on visited
vertices. -/
structure hsearch_map_state (V : Type) [BEq V] [Hashable V] [FinEnum V] where
  /-- The set of visited vertices (as in the reference state). -/
  visited : Finset V
  /-- Path order of every *touched* vertex. -/
  orderMap : Std.HashMap V (ℕ × ℕ)
  /-- Path order of untouched vertices. -/
  orderDefault : ℕ × ℕ
  /-- Mother of every vertex whose mother has been set. -/
  motherMap : Std.HashMap V V
  /-- Fallback mother (never observed on a visited vertex). -/
  motherDefault : V
  /-- The search queue. -/
  stack : List V

namespace hsearch_map_state

variable {g : NatGraph V}

/-- The abstract (reference) search state encoded by a flattened state. -/
@[reducible]
def toBaseState (s : hsearch_map_state V) : hsearch_search_state g where
  visited := s.visited
  pathOrder := fun v => s.orderMap.getD v s.orderDefault
  mother := fun x => s.motherMap.getD x.1 s.motherDefault
  stack := s.stack

/-- The initial flattened state: only `start` is visited, nothing has been recorded yet. -/
def initial (start : V) (d : ℕ × ℕ) : hsearch_map_state V where
  visited := {start}
  orderMap := ∅
  orderDefault := d
  motherMap := ∅
  motherDefault := start
  stack := [start]

omit [LawfulBEq V] in
/-- The initial flattened state encodes the initial reference state. -/
theorem toBaseState_initial (start : V) (d : ℕ × ℕ) :
    (initial start d).toBaseState (g := g) = base_search_state_initial start d := by
  refine base_search_state_eq _ _ ?_ ?_ ?_ ?_
  · rfl
  · funext v; simp [initial]
  · intro x h1 h2; simp [initial]
  · rfl

end hsearch_map_state

instance instHasBaseSearchStateMap (g : NatGraph V) :
    WeightedDiGraph.has_base_search_state g (ℕ × ℕ) (hsearch_map_state V) where
  to_base_state := hsearch_map_state.toBaseState

/-!
## The path order after one expansion, as a stand-alone function
-/

section

variable {g : NatGraph V}

/-- The path order after expanding `head` in state `ps`; this is exactly the `new_order`
computed inside `hsearch_step_expand` and `hsearch_step_expand_gen`. -/
def hsearch_new_order (ps : hsearch_search_state g) (head : V) : V → ℕ × ℕ := fun v =>
  if h : @decide (g.Adj head v) (g.instDecAdj head v) then
    let adj : g.Adj head v := by simp_all only [decide_eq_true_eq]
    if (v ∉ ps.visited) then path_val ps head v adj else new_cost ps head v adj
  else ps.pathOrder v

omit [BEq V] [LawfulBEq V] [Hashable V] in
theorem hsearch_new_order_of_not_adj (ps : hsearch_search_state g) (head v : V)
    (h : ¬ g.Adj head v) : hsearch_new_order ps head v = ps.pathOrder v := by
  simp [hsearch_new_order, h]

omit [BEq V] [LawfulBEq V] [Hashable V] in
theorem hsearch_new_order_of_adj (ps : hsearch_search_state g) (head v : V)
    (h : g.Adj head v) :
    hsearch_new_order ps head v =
      if v ∉ ps.visited then path_val ps head v h else new_cost ps head v h := by
  simp [hsearch_new_order, h]

omit [BEq V] [LawfulBEq V] [Hashable V] in
/-- The `pathOrder` field of the reference expansion step is `hsearch_new_order`. -/
theorem hsearch_step_expand_pathOrder (heur : V → ℕ∞) (ps : hsearch_search_state g)
    (head : V) (tail : List V) :
    (hsearch_step_expand heur ps head tail).pathOrder = hsearch_new_order ps head := rfl

/-- The comparator that keeps the search queue sorted, as a function of the path order. -/
@[reducible]
def hsearch_cmp (heur : V → ℕ∞) (o : V → ℕ × ℕ) : V → V → Bool := fun a b =>
  add_heur a (o a) heur = add_heur b (o b) heur ||
    FValueComp.lt (add_heur a (o a) heur) (add_heur b (o b) heur)

end

/-!
## The expansion step on the flattened state
-/

/-- The per-neighbour data computed by one expansion step: for every neighbour `v` of
`stackHead` its new path order, its new mother, and whether it enters the queue.  Everything
is computed from the *old* maps only, so the order of the insertions is irrelevant. -/
def hsearch_map_items
    (G : NatGraphWithGenerator V)
    (heur : V → ℕ∞)
    (s : hsearch_map_state V)
    (stackHead : V)
    (stackTail : List V) :
    List (V × ((ℕ × ℕ) × V × Bool)) :=
  let g : NatGraph V := G.toWeightedDiGraph
  let ps : hsearch_search_state g := s.toBaseState
  (G.neighbours stackHead).attach.map (fun x =>
    let v : V := x.1
    let adj : g.Adj stackHead v := (G.neighbours_are_adj stackHead v).mpr x.2
    let no : ℕ × ℕ :=
      if v ∉ ps.visited then path_val ps stackHead v adj else new_cost ps stackHead v adj
    let nm : V :=
      if v ∉ ps.visited then stackHead
      else if ps.pathOrder v = no then s.motherMap.getD v s.motherDefault else stackHead
    let isNew : Bool :=
      decide (heur v ≠ ⊤ ∧ (v ∉ ps.visited ∨
        (v ∈ ps.visited ∧ v ∉ stackTail ∧
          (ps.pathOrder v).fst > (ps.pathOrder stackHead).fst + g.edgeCost adj)))
    (v, no, nm, isNew))

/-- The mother relation after expanding `stackHead`, as a stand-alone function. -/
def hsearch_map_new_mother
    (G : NatGraphWithGenerator V) (s : hsearch_map_state V) (stackHead : V) : V → V := fun v =>
  if v ∉ s.visited then stackHead
  else if (s.toBaseState (g := G.toWeightedDiGraph)).pathOrder v
      = hsearch_new_order (g := G.toWeightedDiGraph) s.toBaseState stackHead v then
    s.motherMap.getD v s.motherDefault
  else stackHead

/-- One expansion step of the heuristic search on the flattened state.

Neighbours are obtained from the generator (as in `hsearch_step_expand_gen`, so no
adjacency decision is performed and the vertex set is never enumerated), and the new path
orders / mothers are *inserted into hash maps* instead of being wrapped in a closure. -/
def hsearch_step_expand_map
    (G : NatGraphWithGenerator V)
    (heur : V → ℕ∞)
    (s : hsearch_map_state V)
    (stackHead : V)
    (stackTail : List V) :
    hsearch_map_state V :=
  -- TEMP no trace
  let items := hsearch_map_items G heur s stackHead stackTail
  let newly_visited_list : List V := items.filterMap (fun x => if x.2.2.2 then some x.1 else none)
  let new_orderMap := items.foldl (fun m x => m.insert x.1 x.2.1) s.orderMap
  let new_motherMap := items.foldl (fun m x => m.insert x.1 x.2.2.1) s.motherMap
  let new_order : V → ℕ × ℕ := fun v => new_orderMap.getD v s.orderDefault
  { visited := s.visited ∪ newly_visited_list.toFinset
    orderMap := new_orderMap
    orderDefault := s.orderDefault
    motherMap := new_motherMap
    motherDefault := s.motherDefault
    stack := (stackTail ++ newly_visited_list).mergeSort (fun a b =>
      add_heur a (new_order a) heur = add_heur b (new_order b) heur ||
        FValueComp.lt (add_heur a (new_order a) heur) (add_heur b (new_order b) heur)) }

/-!
## One step produces the same abstract state
-/

/-- The abstract state encoded by a flattened state, for a graph presented by a generator.
Notational convenience: it fixes the (otherwise implicit) graph of `toBaseState`. -/
abbrev hsearch_map_state.toBaseG (G : NatGraphWithGenerator V) (s : hsearch_map_state V) :
    hsearch_search_state G.toWeightedDiGraph := s.toBaseState

section

variable (G : NatGraphWithGenerator V) (heur : V → ℕ∞)
  (s : hsearch_map_state V) (stackHead : V) (stackTail : List V)

/-- The keys of the inserted entries are exactly the neighbours of the expanded node. -/
theorem hsearch_map_items_keys :
    (hsearch_map_items G heur s stackHead stackTail).map Prod.fst = G.neighbours stackHead := by
  simp [hsearch_map_items, List.map_map, Function.comp_def]

/-- Every inserted path order is the value of `hsearch_new_order`. -/
theorem hsearch_map_items_order :
    ∀ x ∈ hsearch_map_items G heur s stackHead stackTail,
      x.2.1 = hsearch_new_order (s.toBaseG G) stackHead x.1 := by
  intro x hx
  simp only [hsearch_map_items, List.mem_map, List.mem_attach, true_and] at hx
  obtain ⟨⟨v, hv⟩, rfl⟩ := hx
  have hadj : (G.toWeightedDiGraph).Adj stackHead v := (G.neighbours_are_adj stackHead v).mpr hv
  simp [hsearch_new_order_of_adj _ _ _ hadj]

/-- Every inserted mother is the value of `hsearch_map_new_mother`. -/
theorem hsearch_map_items_mother :
    ∀ x ∈ hsearch_map_items G heur s stackHead stackTail,
      x.2.2.1 = hsearch_map_new_mother G s stackHead x.1 := by
  intro x hx
  simp only [hsearch_map_items, List.mem_map, List.mem_attach, true_and] at hx
  obtain ⟨⟨v, hv⟩, rfl⟩ := hx
  have hadj : (G.toWeightedDiGraph).Adj stackHead v := (G.neighbours_are_adj stackHead v).mpr hv
  simp [hsearch_map_new_mother, hsearch_new_order_of_adj _ _ _ hadj]

/-- The newly queued vertices are the same as in the generator-based step. -/
theorem hsearch_map_newly_visited_list :
    (hsearch_map_items G heur s stackHead stackTail).filterMap
        (fun x => if x.2.2.2 then some x.1 else none)
      = (G.neighbours stackHead).attach.filterMap
        (fun ⟨v, hv⟩ =>
          let adj : (G.toWeightedDiGraph).Adj stackHead v :=
            (G.neighbours_are_adj stackHead v).mpr hv
          if heur v ≠ ⊤ ∧ (v ∉ (s.toBaseG G).visited ∨
            (v ∈ (s.toBaseG G).visited ∧ v ∉ stackTail ∧
              ((s.toBaseG G).pathOrder v).fst >
                ((s.toBaseG G).pathOrder stackHead).fst + NatGraph.edgeCost adj))
          then some v else none) := by
  simp [hsearch_map_items, List.filterMap_map]

/-- Every newly queued vertex is a neighbour of the expanded node. -/
theorem hsearch_map_newly_subset (x : V)
    (hx : x ∈ (hsearch_map_items G heur s stackHead stackTail).filterMap
      (fun y => if y.2.2.2 then some y.1 else none)) :
    x ∈ G.neighbours stackHead := by
  simp only [List.mem_filterMap] at hx
  obtain ⟨y, hy, hxy⟩ := hx
  have hy1 : y.1 = x := by split at hxy <;> simp_all
  rw [← hsearch_map_items_keys G heur s stackHead stackTail, ← hy1]
  exact List.mem_map_of_mem hy

/-- Value of the updated order map: the new path order of the neighbours, the old value
everywhere else. -/
theorem hsearch_map_orderMap_getD (v : V) :
    ((hsearch_map_items G heur s stackHead stackTail).foldl
        (fun m x => m.insert x.1 x.2.1) s.orderMap).getD v s.orderDefault
      = hsearch_new_order (s.toBaseG G) stackHead v := by
  have h := getD_foldl_insert (hsearch_map_items G heur s stackHead stackTail) Prod.fst
    (fun x => x.2.1) (hsearch_new_order (s.toBaseG G) stackHead)
    (hsearch_map_items_order G heur s stackHead stackTail) s.orderMap v s.orderDefault
  rw [hsearch_map_items_keys] at h
  rw [h]
  by_cases hv : v ∈ G.neighbours stackHead
  · rw [if_pos hv]
  · have hadj : ¬ (G.toWeightedDiGraph).Adj stackHead v := fun h =>
      hv ((G.neighbours_are_adj stackHead v).mp h)
    rw [if_neg hv, hsearch_new_order_of_not_adj _ _ _ hadj]

/-- Value of the updated mother map. -/
theorem hsearch_map_motherMap_getD (x : V) :
    ((hsearch_map_items G heur s stackHead stackTail).foldl
        (fun m y => m.insert y.1 y.2.2.1) s.motherMap).getD x s.motherDefault
      = if x ∈ G.neighbours stackHead then hsearch_map_new_mother G s stackHead x
        else s.motherMap.getD x s.motherDefault := by
  have h := getD_foldl_insert (hsearch_map_items G heur s stackHead stackTail) Prod.fst
    (fun y => y.2.2.1) (hsearch_map_new_mother G s stackHead)
    (hsearch_map_items_mother G heur s stackHead stackTail) s.motherMap x s.motherDefault
  rw [hsearch_map_items_keys] at h
  exact h

/-- The `pathOrder` field agrees with the generator-based step. -/
theorem hsearch_map_pathOrder :
    ((hsearch_step_expand_map G heur s stackHead stackTail).toBaseG G).pathOrder
      = (hsearch_step_expand_gen G heur (s.toBaseG G) stackHead stackTail).pathOrder := by
  rw [hsearch_gen_pathOrder, hsearch_step_expand_pathOrder]
  funext v
  exact hsearch_map_orderMap_getD G heur s stackHead stackTail v

/-- The `visited` field agrees with the generator-based step. -/
theorem hsearch_map_visited :
    ((hsearch_step_expand_map G heur s stackHead stackTail).toBaseG G).visited
      = (hsearch_step_expand_gen G heur (s.toBaseG G) stackHead stackTail).visited := by
  show s.visited ∪ _ = _
  rw [hsearch_map_newly_visited_list]
  congr 1
  refine congrArg List.toFinset (List.filterMap_congr fun x _ => ?_)
  obtain ⟨v, hv⟩ := x
  congr!

/-- The `stack` field agrees with the generator-based step. -/
theorem hsearch_map_stack :
    ((hsearch_step_expand_map G heur s stackHead stackTail).toBaseG G).stack
      = (hsearch_step_expand_gen G heur (s.toBaseG G) stackHead stackTail).stack := by
  show List.mergeSort (stackTail ++ _) _ = _
  congr 1
  · refine congrArg (stackTail ++ ·) ?_
    rw [hsearch_map_newly_visited_list]
    refine List.filterMap_congr fun x _ => ?_
    obtain ⟨v, hv⟩ := x
    congr!
  · funext a b
    simp only [hsearch_map_orderMap_getD]
    rfl

omit [BEq V] [LawfulBEq V] [Hashable V] in
/-- The value of the `mother` field of the generator-based step. -/
theorem hsearch_gen_mother_val (ps : hsearch_search_state G.toWeightedDiGraph)
    (x : V) (hx : x ∈ (hsearch_step_expand_gen G heur ps stackHead stackTail).visited) :
    (hsearch_step_expand_gen G heur ps stackHead stackTail).mother ⟨x, hx⟩
      = if h : x ∉ ps.visited then stackHead
        else if ps.pathOrder x = hsearch_new_order ps stackHead x then
          ps.mother ⟨x, not_not.mp h⟩
        else stackHead := rfl

/-- The `mother` fields agree pointwise. -/
theorem hsearch_map_mother (x : V)
    (h1 : x ∈ ((hsearch_step_expand_map G heur s stackHead stackTail).toBaseG G).visited)
    (h2 : x ∈ (hsearch_step_expand_gen G heur (s.toBaseG G) stackHead stackTail).visited) :
    ((hsearch_step_expand_map G heur s stackHead stackTail).toBaseG G).mother ⟨x, h1⟩
      = (hsearch_step_expand_gen G heur (s.toBaseG G) stackHead stackTail).mother ⟨x, h2⟩ := by
  rw [hsearch_gen_mother_val]
  show ((hsearch_map_items G heur s stackHead stackTail).foldl
      (fun m y => m.insert y.1 y.2.2.1) s.motherMap).getD x s.motherDefault = _
  rw [hsearch_map_motherMap_getD]
  by_cases hx : x ∈ G.neighbours stackHead
  · rw [if_pos hx]
    unfold hsearch_map_new_mother
    congr!
  · rw [if_neg hx]
    have hvis : x ∈ s.visited := by
      have h1' : x ∈ s.visited ∪ ((hsearch_map_items G heur s stackHead stackTail).filterMap
          (fun y => if y.2.2.2 then some y.1 else none)).toFinset := h1
      rcases Finset.mem_union.mp h1' with h | h
      · exact h
      · exact absurd (hsearch_map_newly_subset G heur s stackHead stackTail x
          (List.mem_toFinset.mp h)) hx
    have hadj : ¬ (G.toWeightedDiGraph).Adj stackHead x := fun h =>
      hx ((G.neighbours_are_adj stackHead x).mp h)
    rw [dif_neg (not_not.mpr hvis),
      if_pos (hsearch_new_order_of_not_adj (s.toBaseG G) stackHead x hadj).symm]

/-- **One expansion step of the flattened search produces exactly the same abstract state
as the generator-based step.** -/
theorem hsearch_step_expand_map_eq_gen :
    (hsearch_step_expand_map G heur s stackHead stackTail).toBaseG G
      = hsearch_step_expand_gen G heur (s.toBaseG G) stackHead stackTail :=
  base_search_state_eq _ _
    (hsearch_map_visited G heur s stackHead stackTail)
    (hsearch_map_pathOrder G heur s stackHead stackTail)
    (hsearch_map_mother G heur s stackHead stackTail)
    (hsearch_map_stack G heur s stackHead stackTail)

/-- **One expansion step of the flattened search produces exactly the same abstract state
as the reference implementation `hsearch_step_expand`.** -/
theorem hsearch_step_expand_map_eq :
    (hsearch_step_expand_map G heur s stackHead stackTail).toBaseG G
      = hsearch_step_expand (g := G.toWeightedDiGraph) heur (s.toBaseG G) stackHead stackTail := by
  rw [hsearch_step_expand_map_eq_gen, hsearch_step_expand_gen_eq]

end

end NatGraph
