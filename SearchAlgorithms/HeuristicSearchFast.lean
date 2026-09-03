import SearchAlgorithms.HeuristicSearchMap

/-!
# Heuristic search with a hash-set based `visited` set

`SearchAlgorithms.HeuristicSearchMap` removed the *closure chains* from the search state by
storing the path order and the mother relation in hash maps.  Measuring the resulting
implementation shows that a second, even more expensive, bottleneck remains: the **visited
set**.

The reference state stores `visited : Finset V`, and one expansion step computes

```
new_visited := priorState.visited ∪ newly_visited_list.toFinset
```

`Finset.union` is `Multiset.ndunion`, i.e. a fold that inserts every element of the left-hand
set into the right-hand one, and every `Multiset` insertion scans the set it inserts into.
Building the visited set of a search that expands `n` nodes therefore costs `Θ(n³)`
element comparisons overall (measured: 13 ms for `n = 400`, 170 ms for `n = 800`, 1.3 s for
`n = 1600`).  On top of that, each expansion tests `v ∈ priorState.visited` once per
neighbour, and a `Finset` membership test is a linear scan.

This module keeps the search state of `HeuristicSearchMap` but replaces the visited set by a
`VisitedSet`: a `Finset V` **paired with a `Std.HashSet V` holding the same elements**, the
agreement being a proof field of the structure (and hence erased at run time).

* every membership test goes to the hash set — `O(1)` instead of `O(|visited|)`;
* every insertion is `Finset.cons` (an `O(1)` `Multiset` cons, justified by the hash set
  saying that the element is new) plus an `O(1)` hash-set insertion — instead of an
  `O(|visited|²)` `Finset` union;
* the `Finset` is still *stored*, so the abstraction function into the reference state
  (`WeightedDiGraph.base_search_state`, whose `visited` field is a `Finset`) stays `O(1)`;
  converting a hash set to a `Finset` on every step would reintroduce a linear cost.

## Correctness

As before nothing is re-proved.  The theorem

```
hsearch_step_expand_fast_eq_map :
  (hsearch_step_expand_fast G heur s head tail).toMapState
    = hsearch_step_expand_map G heur s.toMapState head tail
```

says that one expansion produces the *same flattened state* as `HeuristicSearchMap`, and
hence (by `hsearch_step_expand_map_eq`) the same abstract state as the reference
`hsearch_step_expand`; see `hsearch_step_expand_fast_eq`.  Soundness, completeness and
optimality then transfer verbatim through
`WeightedDiGraph.search_exe_with_stack_step_sim'` (see `SearchAlgorithms.AStarFast`).
-/

namespace NatGraph

open WeightedDiGraph

variable {V : Type} [FinEnum V] [BEq V] [LawfulBEq V] [Hashable V]

/-!
## A `Finset` with an attached hash set
-/

/-- A `Finset V` together with a `Std.HashSet V` containing exactly the same elements.

The `Finset` is what the correctness statements talk about; the hash set is what the
algorithm queries.  `agree` is a `Prop` field, so it is erased by the compiler: at run time a
`VisitedSet` is just the pair of the two data structures. -/
structure VisitedSet (V : Type) [DecidableEq V] [BEq V] [Hashable V] where
  /-- The set of elements, as a `Finset`. -/
  toFinset : Finset V
  /-- The same elements, in a hash set. -/
  hashSet : Std.HashSet V
  /-- Both fields contain the same elements. -/
  agree : ∀ v : V, v ∈ hashSet ↔ v ∈ toFinset

namespace VisitedSet

omit [LawfulBEq V] in
/-- A hash-set lookup decides `Finset` membership. -/
theorem contains_eq (p : VisitedSet V) (v : V) :
    p.hashSet.contains v = decide (v ∈ p.toFinset) := by
  have h := p.agree v
  rw [Std.HashSet.mem_iff_contains] at h
  by_cases hv : v ∈ p.toFinset <;> simp_all

/-- Insert an element into both components.  The `Finset` insertion is `Finset.cons`, which
is `O(1)`: the required proof that the element is new comes from the hash set. -/
def insert (p : VisitedSet V) (a : V) : VisitedSet V :=
  if h : p.hashSet.contains a then p
  else
    { toFinset := p.toFinset.cons a (by rw [← p.agree, Std.HashSet.mem_iff_contains]; simp [h])
      hashSet := p.hashSet.insert a
      agree := by
        intro v
        rw [Std.HashSet.mem_insert, Finset.mem_cons, p.agree]
        constructor
        · rintro (h1 | h1)
          · exact Or.inl (eq_of_beq h1).symm
          · exact Or.inr h1
        · rintro (rfl | h1)
          · exact Or.inl (beq_self_eq_true v)
          · exact Or.inr h1 }

@[simp] theorem insert_toFinset (p : VisitedSet V) (a : V) :
    (p.insert a).toFinset = Insert.insert a p.toFinset := by
  unfold VisitedSet.insert
  split
  · next h =>
    have hmem : a ∈ p.toFinset := (p.agree a).mp (Std.HashSet.mem_iff_contains.mpr h)
    exact (Finset.insert_eq_self.mpr hmem).symm
  · next h =>
    exact Finset.cons_eq_insert a p.toFinset
      (by rw [← p.agree, Std.HashSet.mem_iff_contains]; simp [h])

/-- Insert all elements of a list. -/
def insertList (p : VisitedSet V) (l : List V) : VisitedSet V := l.foldl VisitedSet.insert p

/-- Inserting a list adds exactly the elements of the list. -/
theorem insertList_toFinset (p : VisitedSet V) (l : List V) :
    (p.insertList l).toFinset = p.toFinset ∪ l.toFinset := by
  induction l generalizing p with
  | nil => simp [insertList]
  | cons a t ih =>
    simp only [insertList, List.foldl_cons] at *
    rw [ih (p.insert a), insert_toFinset]
    ext x
    simp only [Finset.mem_union, Finset.mem_insert, List.toFinset_cons, List.mem_toFinset]
    tauto

/-- The singleton `VisitedSet`. -/
def singleton (a : V) : VisitedSet V where
  toFinset := {a}
  hashSet := (∅ : Std.HashSet V).insert a
  agree := by
    intro v
    rw [Std.HashSet.mem_insert, Finset.mem_singleton]
    constructor
    · rintro (h1 | h1)
      · exact (eq_of_beq h1).symm
      · simp at h1
    · rintro rfl
      exact Or.inl (beq_self_eq_true v)

@[simp] theorem singleton_toFinset (a : V) : (singleton a).toFinset = ({a} : Finset V) := rfl

end VisitedSet

/-!
## The search state
-/

/-- A heuristic-search state whose path order and mother relation live in hash maps (as in
`hsearch_map_state`) and whose visited set is a `VisitedSet`, i.e. a `Finset` with an
attached hash set for `O(1)` membership tests and `O(1)` insertions. -/
structure hsearch_fast_state (V : Type) [BEq V] [Hashable V] [FinEnum V] where
  /-- The visited vertices (`Finset` + hash set). -/
  vis : VisitedSet V
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

namespace hsearch_fast_state

variable {g : NatGraph V}

/-- Forgetting the hash set gives the flattened state of `SearchAlgorithms.HeuristicSearchMap`.
This is the translation along which all correctness results are transferred; it is never
evaluated at run time. -/
def toMapState (s : hsearch_fast_state V) : hsearch_map_state V where
  visited := s.vis.toFinset
  orderMap := s.orderMap
  orderDefault := s.orderDefault
  motherMap := s.motherMap
  motherDefault := s.motherDefault
  stack := s.stack

/-- The abstract (reference) search state encoded by a fast state. -/
@[reducible]
def toBaseState (s : hsearch_fast_state V) : hsearch_search_state g where
  visited := s.vis.toFinset
  pathOrder := fun v => s.orderMap.getD v s.orderDefault
  mother := fun x => s.motherMap.getD x.1 s.motherDefault
  stack := s.stack

theorem toBaseState_eq_toMapState (s : hsearch_fast_state V) :
    s.toBaseState (g := g) = s.toMapState.toBaseState := rfl

/-- The initial fast state: only `start` is visited, nothing has been recorded yet. -/
def initial (start : V) (d : ℕ × ℕ) : hsearch_fast_state V where
  vis := VisitedSet.singleton start
  orderMap := ∅
  orderDefault := d
  motherMap := ∅
  motherDefault := start
  stack := [start]

theorem toMapState_initial (start : V) (d : ℕ × ℕ) :
    (initial start d).toMapState = hsearch_map_state.initial start d := rfl

/-- The initial fast state encodes the initial reference state. -/
theorem toBaseState_initial (start : V) (d : ℕ × ℕ) :
    (initial start d).toBaseState (g := g) = base_search_state_initial start d := by
  rw [toBaseState_eq_toMapState, toMapState_initial]
  exact hsearch_map_state.toBaseState_initial start d

end hsearch_fast_state

instance instHasBaseSearchStateFast (g : NatGraph V) :
    WeightedDiGraph.has_base_search_state g (ℕ × ℕ) (hsearch_fast_state V) where
  to_base_state := hsearch_fast_state.toBaseState

/-!
## The expansion step
-/

/-- The per-neighbour data computed by one expansion step, exactly as in
`hsearch_map_items` — except that the test "has `v` been visited?" is a hash-set lookup
instead of a linear scan through a `Finset`. -/
def hsearch_fast_items
    (G : NatGraphWithGenerator V)
    (heur : V → ℕ∞)
    (s : hsearch_fast_state V)
    (stackHead : V)
    (stackTail : List V) :
    List (V × ((ℕ × ℕ) × V × Bool)) :=
  let g : NatGraph V := G.toWeightedDiGraph
  let ps : hsearch_search_state g := s.toBaseState
  (G.neighbours stackHead).attach.map (fun x =>
    let v : V := x.1
    let adj : g.Adj stackHead v := (G.neighbours_are_adj stackHead v).mpr x.2
    let isVisited : Bool := s.vis.hashSet.contains v
    let no : ℕ × ℕ :=
      if isVisited then new_cost ps stackHead v adj else path_val ps stackHead v adj
    let nm : V :=
      if isVisited then
        (if ps.pathOrder v = no then s.motherMap.getD v s.motherDefault else stackHead)
      else stackHead
    let isNew : Bool :=
      decide (heur v ≠ ⊤) &&
        (!isVisited ||
          (decide (v ∉ stackTail) &&
            decide ((ps.pathOrder v).fst > (ps.pathOrder stackHead).fst + g.edgeCost adj)))
    (v, no, nm, isNew))

/-- One expansion step on the fast state.

Identical to `hsearch_step_expand_map` except for the visited set: membership is decided by
the hash set and the newly visited vertices are `cons`-ed on, instead of computing a
`Finset` union. -/
def hsearch_step_expand_fast
    (G : NatGraphWithGenerator V)
    (heur : V → ℕ∞)
    (s : hsearch_fast_state V)
    (stackHead : V)
    (stackTail : List V) :
    hsearch_fast_state V :=
  let items := hsearch_fast_items G heur s stackHead stackTail
  let newly_visited_list : List V := items.filterMap (fun x => if x.2.2.2 then some x.1 else none)
  let new_orderMap := items.foldl (fun m x => m.insert x.1 x.2.1) s.orderMap
  let new_motherMap := items.foldl (fun m x => m.insert x.1 x.2.2.1) s.motherMap
  let new_order : V → ℕ × ℕ := fun v => new_orderMap.getD v s.orderDefault
  { vis := s.vis.insertList newly_visited_list
    orderMap := new_orderMap
    orderDefault := s.orderDefault
    motherMap := new_motherMap
    motherDefault := s.motherDefault
    stack := (stackTail ++ newly_visited_list).mergeSort (fun a b =>
      add_heur a (new_order a) heur = add_heur b (new_order b) heur ||
        FValueComp.lt (add_heur a (new_order a) heur) (add_heur b (new_order b) heur)) }

/-!
## One step produces the same flattened state
-/

section

variable (G : NatGraphWithGenerator V) (heur : V → ℕ∞)
  (s : hsearch_fast_state V) (stackHead : V) (stackTail : List V)

/-- The per-neighbour data is the same as the one computed by `HeuristicSearchMap`: the two
differ only in *how* the visited test is performed. -/
theorem hsearch_fast_items_eq :
    hsearch_fast_items G heur s stackHead stackTail
      = hsearch_map_items G heur s.toMapState stackHead stackTail := by
  unfold hsearch_fast_items hsearch_map_items
  refine List.map_congr_left ?_
  rintro ⟨v, hv⟩ -
  have hc : s.vis.hashSet.contains v = decide (v ∈ s.vis.toFinset) :=
    VisitedSet.contains_eq s.vis v
  simp only [hsearch_fast_state.toMapState, hc]
  by_cases hvis : v ∈ s.vis.toFinset <;> simp [hvis]

/-- **One expansion step of the fast search produces exactly the same flattened state as
`hsearch_step_expand_map`.** -/
theorem hsearch_step_expand_fast_eq_map :
    (hsearch_step_expand_fast G heur s stackHead stackTail).toMapState
      = hsearch_step_expand_map G heur s.toMapState stackHead stackTail := by
  unfold hsearch_step_expand_fast hsearch_step_expand_map
  simp only [hsearch_fast_items_eq, hsearch_fast_state.toMapState,
    VisitedSet.insertList_toFinset]
  rfl

/-- **One expansion step of the fast search produces exactly the same abstract state as the
reference implementation `hsearch_step_expand`.** -/
theorem hsearch_step_expand_fast_eq :
    (hsearch_step_expand_fast G heur s stackHead stackTail).toBaseState
        (g := G.toWeightedDiGraph)
      = hsearch_step_expand (g := G.toWeightedDiGraph) heur
          (s.toBaseState (g := G.toWeightedDiGraph)) stackHead stackTail := by
  rw [hsearch_fast_state.toBaseState_eq_toMapState, hsearch_step_expand_fast_eq_map,
    hsearch_fast_state.toBaseState_eq_toMapState]
  exact hsearch_step_expand_map_eq G heur s.toMapState stackHead stackTail

end

end NatGraph
