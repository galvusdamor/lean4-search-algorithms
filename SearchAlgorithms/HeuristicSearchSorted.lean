import SearchAlgorithms.HeuristicSearchFast
import SearchAlgorithms.MergeSortLemmas
import SearchAlgorithms.SearchSimStack

/-!
# Heuristic search with a queue that is *kept* sorted

`SearchAlgorithms.HeuristicSearchFast` made every expansion independent of the number of
already visited nodes.  What remains linear (indeed super-linear) in the size of the search
**queue** is the queue handling itself: the reference expansion step computes

```
new_stack = (stackTail ++ newly_visited_list).mergeSort cmp
```

i.e. it re-sorts the whole queue after every single expansion (`Θ(m log m)` comparisons for a
queue of length `m`, each comparison being two path-order lookups), and it tests
`v ∉ stackTail` by scanning the queue once per neighbour.

This module removes both costs while computing *literally the same* queue:

* the queue is **kept sorted**.  If no queued node changed its path order during the
  expansion — which the step detects in `O(out-degree)` — the new queue is obtained by a
  single `List.merge` of the (already sorted) old queue with the sorted list of new nodes.
  By `SortAux.mergeSort_append_of_pairwise_left` this is the same list as the full
  `mergeSort`; and since `List.merge xs [] = xs`, an expansion that queues nothing is `O(1)`
  and shares the whole queue.  Only when a queued node's order actually changed (a
  "decrease-key") does the step fall back to a full `mergeSort`.
* the queue is accompanied by a `Std.HashMap V ℕ` of *multiplicities*, so `v ∉ stackTail`
  is an `O(1)` lookup instead of a scan.

Both facts are invariants of the state, recorded as (compile-time only) proof fields of
`hsearch_sorted_state`, so they hold for every value of the type — no separate reachability
argument is needed.  Because the invariants relate the queue to the *state's* stack, the
expansion function reads `head`/`tail` off its own state; it is proved equal to the reference
expansion whenever the search loop calls it, i.e. whenever `stack = head :: tail`, and that
weaker hypothesis is exactly what `WeightedDiGraph.search_exe_with_stack_step_sim_of_stack`
needs to transfer soundness, completeness and optimality (see
`SearchAlgorithms.AStarSorted`).

## Two implementation details that matter for the run time

Both are invisible in the statements (all the definitions below are unchanged mathematically)
but each of them costs a factor that grows with the size of the search:

* **share the intermediate results.**  `hsearch_expand_sorted_core` spells its body out with
  `let`s.  In particular the comparator closes over the *finished* order map; writing it as
  `hsearch_queue_le heur (hsearch_sorted_new_order …)` instead would rebuild that map inside
  every single comparison.
* **do not touch the old maps after updating them.**  A `Std.HashMap` is updated in place
  only when the reference to it is unique, so `mustResort` — the last read of the *old* order
  map — is computed *before* the map is updated; otherwise the first `insert` copies the whole
  map, which makes every expansion cost `O(|touched vertices|)`.  For the same reason
  `countsDec` erases a vertex that leaves the queue instead of storing a `0`, which keeps the
  multiplicity map as small as the queue.

## Measured effect (`lake exe bench`, `lake exe benchbroom`)

On the "broom" graph, where the first expansion fills the queue with `|V| - 1` nodes and every
later expansion pops one of them, Dijkstra with the fast state takes 0.27 s for `|V| = 1000`
and 1.33 s for `|V| = 2000` (quadratic), while the sorted queue needs 2.4 ms and 2.6 ms.  On
the path graph the per-expansion time of both is flat (≈ 0.5 µs/step over 3000 expansions).
-/

namespace NatGraph

open WeightedDiGraph

variable {V : Type} [FinEnum V] [BEq V] [LawfulBEq V] [Hashable V]

/-!
## The queue comparator
-/

/-- The comparator that keeps the search queue sorted: compare the `f`-values (path order
plus heuristic), where `a` comes first if the two are equal. -/
def hsearch_queue_le (heur : V → ℕ∞) (o : V → ℕ × ℕ) (a b : V) : Bool :=
  add_heur a (o a) heur = add_heur b (o b) heur ||
    FValueComp.lt (add_heur a (o a) heur) (add_heur b (o b) heur)

omit [FinEnum V] [BEq V] [LawfulBEq V] [Hashable V] in
theorem hsearch_queue_le_trans (heur : V → ℕ∞) (o : V → ℕ × ℕ) (a b c : V) :
    hsearch_queue_le heur o a b → hsearch_queue_le heur o b c → hsearch_queue_le heur o a c :=
  fun h1 h2 => hsearch_merge_trans _ _ _ h1 h2

omit [FinEnum V] [BEq V] [LawfulBEq V] [Hashable V] in
theorem hsearch_queue_le_total (heur : V → ℕ∞) (o : V → ℕ × ℕ) (a b : V) :
    (hsearch_queue_le heur o a b || hsearch_queue_le heur o b a) = true :=
  hsearch_merge_total _ _

omit [FinEnum V] [BEq V] [LawfulBEq V] [Hashable V] in
/-- The comparator only depends on the path order of the elements compared. -/
theorem hsearch_queue_le_congr (heur : V → ℕ∞) (o o' : V → ℕ × ℕ) (a b : V)
    (ha : o a = o' a) (hb : o b = o' b) :
    hsearch_queue_le heur o a b = hsearch_queue_le heur o' a b := by
  simp only [hsearch_queue_le, ha, hb]

/-!
## Multiplicities of the queue elements
-/

/-- Increment the multiplicity of `a`. -/
def countsInc (m : Std.HashMap V ℕ) (a : V) : Std.HashMap V ℕ := m.insert a (m.getD a 0 + 1)

/-- Increment the multiplicity of every element of `l`. -/
def countsIncList (m : Std.HashMap V ℕ) (l : List V) : Std.HashMap V ℕ := l.foldl countsInc m

/-- Decrement the multiplicity of `a`; a vertex that leaves the queue is *removed* from the
map, so that the map stays as small as the queue instead of growing with the number of
expansions. -/
def countsDec (m : Std.HashMap V ℕ) (a : V) : Std.HashMap V ℕ :=
  if m.getD a 0 ≤ 1 then m.erase a else m.insert a (m.getD a 0 - 1)

theorem countsInc_getD (m : Std.HashMap V ℕ) (a v : V) :
    (countsInc m a).getD v 0 = m.getD v 0 + (if v = a then 1 else 0) := by
  unfold countsInc
  rw [Std.HashMap.getD_insert]
  by_cases h : v = a
  · subst h; simp
  · simp [h, Ne.symm h]

theorem countsDec_getD (m : Std.HashMap V ℕ) (a v : V) :
    (countsDec m a).getD v 0 = m.getD v 0 - (if v = a then 1 else 0) := by
  unfold countsDec
  split
  · next hc =>
    rw [Std.HashMap.getD_erase]
    by_cases h : v = a
    · subst h; simp; omega
    · simp [h, Ne.symm h]
  · rw [Std.HashMap.getD_insert]
    by_cases h : v = a
    · subst h; simp
    · simp [h, Ne.symm h]

theorem countsIncList_getD (m : Std.HashMap V ℕ) (l : List V) (v : V) :
    (countsIncList m l).getD v 0 = m.getD v 0 + l.count v := by
  induction l generalizing m with
  | nil => simp [countsIncList]
  | cons a t ih =>
    rw [countsIncList, List.foldl_cons, ← countsIncList, ih, countsInc_getD, List.count_cons]
    by_cases h : v = a
    · subst h; simp [Nat.add_assoc, Nat.add_comm]
    · simp [h, Ne.symm h]

/-!
## The search state
-/

/-- A search state whose queue is *known to be sorted* and comes with the multiplicities of
its elements.

In addition to the data of `hsearch_fast_state` (hash maps for the path order and the mother
relation, hash-set backed visited set) it stores `counts`, the multiplicity of every vertex
in `stack`.  The two `Prop` fields `counts_spec` and `stack_sorted` are erased by the
compiler; they let the expansion step *maintain* the queue instead of re-sorting it, and test
queue membership in constant time. -/
structure hsearch_sorted_state (V : Type) [BEq V] [Hashable V] [FinEnum V]
    (heur : V → ℕ∞) where
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
  /-- The search queue, sorted by `hsearch_queue_le`. -/
  stack : List V
  /-- Multiplicity of every vertex in `stack`. -/
  counts : Std.HashMap V ℕ
  /-- `counts` really are the multiplicities of the queue elements. -/
  counts_spec : ∀ v : V, counts.getD v 0 = stack.count v
  /-- The queue is sorted. -/
  stack_sorted : stack.Pairwise
    (fun a b => hsearch_queue_le heur (fun v => orderMap.getD v orderDefault) a b = true)

namespace hsearch_sorted_state

variable {g : NatGraph V} {heur : V → ℕ∞}

/-- Forgetting the queue invariants gives the state of `SearchAlgorithms.HeuristicSearchFast`.
This is the translation along which all correctness results are transferred; it is never
evaluated at run time. -/
def toFastState (s : hsearch_sorted_state V heur) : hsearch_fast_state V where
  vis := s.vis
  orderMap := s.orderMap
  orderDefault := s.orderDefault
  motherMap := s.motherMap
  motherDefault := s.motherDefault
  stack := s.stack

/-- The abstract (reference) search state encoded by a sorted state. -/
@[reducible]
def toBaseState (s : hsearch_sorted_state V heur) : hsearch_search_state g where
  visited := s.vis.toFinset
  pathOrder := fun v => s.orderMap.getD v s.orderDefault
  mother := fun x => s.motherMap.getD x.1 s.motherDefault
  stack := s.stack

omit [LawfulBEq V] in
theorem toBaseState_eq_toFastState (s : hsearch_sorted_state V heur) :
    s.toBaseState (g := g) = s.toFastState.toBaseState := rfl

/-- The initial sorted state: only `start` is visited, the queue is the singleton `[start]`. -/
def initial (heur : V → ℕ∞) (start : V) (d : ℕ × ℕ) : hsearch_sorted_state V heur where
  vis := VisitedSet.singleton start
  orderMap := ∅
  orderDefault := d
  motherMap := ∅
  motherDefault := start
  stack := [start]
  counts := (∅ : Std.HashMap V ℕ).insert start 1
  counts_spec := by
    intro v
    rw [Std.HashMap.getD_insert]
    by_cases h : v = start
    · subst h; simp
    · simp [Ne.symm h]
  stack_sorted := List.pairwise_singleton _ _

theorem toFastState_initial (heur : V → ℕ∞) (start : V) (d : ℕ × ℕ) :
    (initial heur start d).toFastState = hsearch_fast_state.initial start d := rfl

/-- The initial sorted state encodes the initial reference state. -/
theorem toBaseState_initial (heur : V → ℕ∞) (start : V) (d : ℕ × ℕ) :
    (initial heur start d).toBaseState (g := g) = base_search_state_initial start d := by
  rw [toBaseState_eq_toFastState, toFastState_initial]
  exact hsearch_fast_state.toBaseState_initial start d

end hsearch_sorted_state

instance instHasBaseSearchStateSorted (g : NatGraph V) (heur : V → ℕ∞) :
    WeightedDiGraph.has_base_search_state g (ℕ × ℕ) (hsearch_sorted_state V heur) where
  to_base_state := hsearch_sorted_state.toBaseState

/-!
## The pieces of one expansion step
-/

section

variable (G : NatGraphWithGenerator V) (heur : V → ℕ∞)
  (s : hsearch_sorted_state V heur) (head : V)

/-- Multiplicity of `v` in the queue *after* removing the expanded node `head`. -/
def hsearch_count_in_tail_of {heur : V → ℕ∞} (s : hsearch_sorted_state V heur) (head v : V) :
    ℕ :=
  if v == head then s.counts.getD v 0 - 1 else s.counts.getD v 0

/-- The per-neighbour data of one expansion, as in `hsearch_fast_items` — except that the
test `v ∉ stackTail` is a multiplicity lookup instead of a scan through the queue. -/
def hsearch_sorted_items : List (V × ((ℕ × ℕ) × V × Bool)) :=
  let g : NatGraph V := G.toWeightedDiGraph
  let ps : hsearch_search_state g := s.toBaseState
  (G.neighbours head).attach.map (fun x =>
    let v : V := x.1
    let adj : g.Adj head v := (G.neighbours_are_adj head v).mpr x.2
    let isVisited : Bool := s.vis.hashSet.contains v
    let no : ℕ × ℕ := if isVisited then new_cost ps head v adj else path_val ps head v adj
    let nm : V :=
      if isVisited then
        (if ps.pathOrder v = no then s.motherMap.getD v s.motherDefault else head)
      else head
    let isNew : Bool :=
      decide (heur v ≠ ⊤) &&
        (!isVisited ||
          (decide (hsearch_count_in_tail_of s head v = 0) &&
            decide ((ps.pathOrder v).fst > (ps.pathOrder head).fst + g.edgeCost adj)))
    (v, no, nm, isNew))

/-- The vertices entering the queue in this expansion. -/
def hsearch_sorted_newly : List V :=
  (hsearch_sorted_items G heur s head).filterMap (fun x => if x.2.2.2 then some x.1 else none)

/-- The updated path-order map. -/
def hsearch_sorted_orderMap : Std.HashMap V (ℕ × ℕ) :=
  (hsearch_sorted_items G heur s head).foldl (fun m x => m.insert x.1 x.2.1) s.orderMap

/-- The updated mother map. -/
def hsearch_sorted_motherMap : Std.HashMap V V :=
  (hsearch_sorted_items G heur s head).foldl (fun m x => m.insert x.1 x.2.2.1) s.motherMap

/-- The path order after the expansion. -/
def hsearch_sorted_new_order : V → ℕ × ℕ :=
  fun v => (hsearch_sorted_orderMap G heur s head).getD v s.orderDefault

/-- Did the expansion change the path order of a vertex that is still in the queue?  If not,
the queue stays sorted and can be re-used; this is an `O(out-degree)` test. -/
def hsearch_sorted_mustResort : Bool :=
  (hsearch_sorted_items G heur s head).any
    (fun x => (!(x.2.1 == s.orderMap.getD x.1 s.orderDefault))
      && decide (hsearch_count_in_tail_of s head x.1 ≠ 0))

/-- The queue after the expansion: a single `merge` into the (still sorted) old queue, or —
if some queued node changed its path order — a full re-sort. -/
def hsearch_sorted_stack (tail : List V) : List V :=
  let cmp := hsearch_queue_le heur (hsearch_sorted_new_order G heur s head)
  if hsearch_sorted_mustResort G heur s head then
    (tail ++ hsearch_sorted_newly G heur s head).mergeSort cmp
  else
    tail.merge ((hsearch_sorted_newly G heur s head).mergeSort cmp) cmp

/-- The updated multiplicities: the expanded node leaves the queue, the new nodes enter it. -/
def hsearch_sorted_counts : Std.HashMap V ℕ :=
  countsIncList (countsDec s.counts head) (hsearch_sorted_newly G heur s head)

end

/-!
## The expansion step
-/

section

variable (G : NatGraphWithGenerator V) (heur : V → ℕ∞)

/-- The stored multiplicity, minus the expanded node, is the multiplicity in the remaining
queue. -/
theorem hsearch_count_in_tail_of_eq (s : hsearch_sorted_state V heur) (head : V)
    (tail : List V) (hst : s.stack = head :: tail) (v : V) :
    hsearch_count_in_tail_of s head v = tail.count v := by
  unfold hsearch_count_in_tail_of
  rw [s.counts_spec, hst, List.count_cons]
  by_cases h : v = head
  · subst h; simp
  · simp [h, Ne.symm h]

/-- The per-neighbour data is the one of `HeuristicSearchFast`: the two differ only in how
the test `v ∉ stackTail` is performed. -/
theorem hsearch_sorted_items_eq (s : hsearch_sorted_state V heur) (head : V) (tail : List V)
    (hst : s.stack = head :: tail) :
    hsearch_sorted_items G heur s head
      = hsearch_fast_items G heur s.toFastState head tail := by
  unfold hsearch_sorted_items hsearch_fast_items
  refine List.map_congr_left ?_
  rintro ⟨v, hv⟩ -
  have hc := hsearch_count_in_tail_of_eq heur s head tail hst v
  simp only [hsearch_sorted_state.toFastState, hc, List.count_eq_zero]
  rfl

/-- The path order after the expansion, as computed by `HeuristicSearchMap`. -/
theorem hsearch_sorted_new_order_eq (s : hsearch_sorted_state V heur) (head : V)
    (tail : List V) (hst : s.stack = head :: tail) (v : V) :
    hsearch_sorted_new_order G heur s head v
      = hsearch_new_order (s.toFastState.toMapState.toBaseG G) head v := by
  unfold hsearch_sorted_new_order hsearch_sorted_orderMap
  rw [hsearch_sorted_items_eq G heur s head tail hst,
    hsearch_fast_items_eq G heur s.toFastState head tail]
  exact hsearch_map_orderMap_getD G heur s.toFastState.toMapState head tail v

/-- If the expansion did not change the path order of any queued node, then the path order of
every node of the remaining queue is unchanged. -/
theorem hsearch_sorted_new_order_eq_old (s : hsearch_sorted_state V heur) (head : V)
    (tail : List V) (hst : s.stack = head :: tail)
    (hmust : hsearch_sorted_mustResort G heur s head = false) (v : V) (hv : v ∈ tail) :
    hsearch_sorted_new_order G heur s head v = s.orderMap.getD v s.orderDefault := by
  rw [hsearch_sorted_new_order_eq G heur s head tail hst]
  by_cases hadj : (G.toWeightedDiGraph).Adj head v
  · -- `v` is a neighbour: its item says that its order did not change
    have hvn : v ∈ G.neighbours head := (G.neighbours_are_adj head v).mp hadj
    have hkeys := hsearch_map_items_keys G heur s.toFastState.toMapState head tail
    have hmem : ∃ x ∈ hsearch_map_items G heur s.toFastState.toMapState head tail, x.1 = v := by
      have : v ∈ (hsearch_map_items G heur s.toFastState.toMapState head tail).map Prod.fst := by
        rw [hkeys]; exact hvn
      simpa using this
    obtain ⟨x, hx, hxv⟩ := hmem
    have hxo := hsearch_map_items_order G heur s.toFastState.toMapState head tail x hx
    -- the item is also an item of the sorted state
    have hxs : x ∈ hsearch_sorted_items G heur s head := by
      rw [hsearch_sorted_items_eq G heur s head tail hst,
        hsearch_fast_items_eq G heur s.toFastState head tail]
      exact hx
    have hall : ((!(x.2.1 == s.orderMap.getD x.1 s.orderDefault))
        && decide (hsearch_count_in_tail_of s head x.1 ≠ 0)) = false := by
      simpa using List.any_eq_false.mp hmust x hxs
    have hct : hsearch_count_in_tail_of s head x.1 ≠ 0 := by
      rw [hsearch_count_in_tail_of_eq heur s head tail hst, hxv]
      exact fun h => absurd (List.count_eq_zero.mp h) (by simpa using hv)
    have hxeq : x.2.1 = s.orderMap.getD x.1 s.orderDefault := by
      rcases Bool.and_eq_false_iff.mp hall with h | h
      · simpa using h
      · exact absurd (by simpa using h) hct
    rw [← hxv, ← hxo, hxeq]
  · rw [hsearch_new_order_of_not_adj _ _ _ hadj]
    rfl

/-- If nothing changed in the queue, the queue is still sorted for the *new* path order. -/
theorem hsearch_sorted_tail_pairwise (s : hsearch_sorted_state V heur) (head : V)
    (tail : List V) (hst : s.stack = head :: tail)
    (hmust : hsearch_sorted_mustResort G heur s head = false) :
    tail.Pairwise
      (fun a b => hsearch_queue_le heur (hsearch_sorted_new_order G heur s head) a b = true) := by
  have hold : tail.Pairwise (fun a b =>
      hsearch_queue_le heur (fun v => s.orderMap.getD v s.orderDefault) a b = true) := by
    have := s.stack_sorted
    rw [hst] at this
    exact this.of_cons
  refine hold.imp_of_mem ?_
  intro a b ha hb hab
  rw [hsearch_queue_le_congr heur _ (hsearch_sorted_new_order G heur s head) a b
    (hsearch_sorted_new_order_eq_old G heur s head tail hst hmust a ha).symm
    (hsearch_sorted_new_order_eq_old G heur s head tail hst hmust b hb).symm] at hab
  exact hab

/-- **The maintained queue is the queue of the reference implementation**: merging the new
nodes into the sorted queue gives the same list as re-sorting the whole queue. -/
theorem hsearch_sorted_stack_eq (s : hsearch_sorted_state V heur) (head : V) (tail : List V)
    (hst : s.stack = head :: tail) :
    hsearch_sorted_stack G heur s head tail
      = (tail ++ hsearch_sorted_newly G heur s head).mergeSort
          (hsearch_queue_le heur (hsearch_sorted_new_order G heur s head)) := by
  unfold hsearch_sorted_stack
  split
  · rfl
  · next hmust =>
    exact (SortAux.mergeSort_append_of_pairwise_left _
      (hsearch_queue_le_trans heur (hsearch_sorted_new_order G heur s head))
      (hsearch_queue_le_total heur (hsearch_sorted_new_order G heur s head)) _
      (hsearch_sorted_tail_pairwise G heur s head tail hst
        (by simpa using hmust))).symm

/-- The new queue is a permutation of `tail ++ newly`. -/
theorem hsearch_sorted_stack_perm (s : hsearch_sorted_state V heur) (head : V) (tail : List V)
    (hst : s.stack = head :: tail) :
    (hsearch_sorted_stack G heur s head tail).Perm
      (tail ++ hsearch_sorted_newly G heur s head) := by
  rw [hsearch_sorted_stack_eq G heur s head tail hst]
  exact List.mergeSort_perm _ _

/-- The multiplicities are maintained. -/
theorem hsearch_sorted_counts_spec (s : hsearch_sorted_state V heur) (head : V) (tail : List V)
    (hst : s.stack = head :: tail) (v : V) :
    (hsearch_sorted_counts G heur s head).getD v 0
      = (hsearch_sorted_stack G heur s head tail).count v := by
  rw [(hsearch_sorted_stack_perm G heur s head tail hst).count_eq, List.count_append]
  unfold hsearch_sorted_counts
  rw [countsIncList_getD, countsDec_getD, s.counts_spec, hst, List.count_cons]
  by_cases h : v = head
  · subst h; simp
  · simp [h, Ne.symm h]

/-- The new queue is sorted. -/
theorem hsearch_sorted_stack_sorted (s : hsearch_sorted_state V heur) (head : V) (tail : List V)
    (hst : s.stack = head :: tail) :
    (hsearch_sorted_stack G heur s head tail).Pairwise
      (fun a b => hsearch_queue_le heur
        (fun v => (hsearch_sorted_orderMap G heur s head).getD v s.orderDefault) a b = true) := by
  rw [hsearch_sorted_stack_eq G heur s head tail hst]
  exact List.pairwise_mergeSort
    (hsearch_queue_le_trans heur (hsearch_sorted_new_order G heur s head))
    (hsearch_queue_le_total heur (hsearch_sorted_new_order G heur s head)) _

/-- One expansion step with a maintained queue, given the decomposition of the queue.

The body is spelled out with `let`s (instead of calling the `hsearch_sorted_*` definitions
above) so that the per-neighbour data and, crucially, the **new order map** are computed
exactly once and *shared*: the queue comparator closes over the finished map instead of
rebuilding it at every comparison.  Every field is definitionally the corresponding
`hsearch_sorted_*` value, which is why the two proof fields typecheck. -/
def hsearch_expand_sorted_core (s : hsearch_sorted_state V heur) (head : V) (tail : List V)
    (hst : s.stack = head :: tail) : hsearch_sorted_state V heur :=
  let items := hsearch_sorted_items G heur s head
  let newly : List V := items.filterMap (fun x => if x.2.2.2 then some x.1 else none)
  -- `mustResort` is computed *before* the new maps: it is the last read of `s.orderMap`, so
  -- the fold below can update that map in place instead of copying it.
  let mustResort : Bool := items.any
    (fun x => (!(x.2.1 == s.orderMap.getD x.1 s.orderDefault))
      && decide (hsearch_count_in_tail_of s head x.1 ≠ 0))
  let newOrderMap := items.foldl (fun m x => m.insert x.1 x.2.1) s.orderMap
  let newMotherMap := items.foldl (fun m x => m.insert x.1 x.2.2.1) s.motherMap
  let cmp := hsearch_queue_le heur (fun v => newOrderMap.getD v s.orderDefault)
  { vis := s.vis.insertList newly
    orderMap := newOrderMap
    orderDefault := s.orderDefault
    motherMap := newMotherMap
    motherDefault := s.motherDefault
    stack :=
      if mustResort then (tail ++ newly).mergeSort cmp
      else tail.merge (newly.mergeSort cmp) cmp
    counts := countsIncList (countsDec s.counts head) newly
    counts_spec := by
      show ∀ v : V, (hsearch_sorted_counts G heur s head).getD v 0
        = (hsearch_sorted_stack G heur s head tail).count v
      exact hsearch_sorted_counts_spec G heur s head tail hst
    stack_sorted := by
      show (hsearch_sorted_stack G heur s head tail).Pairwise
        (fun a b => hsearch_queue_le heur
          (fun v => (hsearch_sorted_orderMap G heur s head).getD v s.orderDefault) a b = true)
      exact hsearch_sorted_stack_sorted G heur s head tail hst }

/-- One expansion step with a maintained queue.

The expanded node and the remaining queue are read off the state itself (they agree with the
arguments whenever the search loop calls the function, i.e. whenever `stack = head :: tail`);
this is what makes the queue invariants of the resulting state available. -/
def hsearch_step_expand_sorted (s : hsearch_sorted_state V heur) (_head : V)
    (_tail : List V) : hsearch_sorted_state V heur :=
  match hst : s.stack with
  | [] => s
  | head :: tail => hsearch_expand_sorted_core G heur s head tail hst

/-- When applied to the queue of its own state, the expansion step is
`hsearch_expand_sorted_core`. -/
theorem hsearch_step_expand_sorted_eq_core (s : hsearch_sorted_state V heur) (head : V)
    (tail : List V) (hst : s.stack = head :: tail) :
    hsearch_step_expand_sorted G heur s head tail
      = hsearch_expand_sorted_core G heur s head tail hst := by
  unfold hsearch_step_expand_sorted
  split
  · next h => rw [hst] at h; exact absurd h (by simp)
  · next head' tail' h =>
    rw [hst] at h
    obtain ⟨rfl, rfl⟩ := List.cons.inj h
    rfl

/-!
## One step produces the same state as `HeuristicSearchFast`
-/

/-- The fields of the expansion step are the `hsearch_sorted_*` values (the `let`s of
`hsearch_expand_sorted_core` only make the computation share its intermediate results). -/
theorem hsearch_expand_sorted_core_toFastState (s : hsearch_sorted_state V heur) (head : V)
    (tail : List V) (hst : s.stack = head :: tail) :
    (hsearch_expand_sorted_core G heur s head tail hst).toFastState
      = { vis := s.vis.insertList (hsearch_sorted_newly G heur s head)
          orderMap := hsearch_sorted_orderMap G heur s head
          orderDefault := s.orderDefault
          motherMap := hsearch_sorted_motherMap G heur s head
          motherDefault := s.motherDefault
          stack := hsearch_sorted_stack G heur s head tail } := rfl

/-- **One expansion step of the sorted search produces exactly the same state as the fast
search of `SearchAlgorithms.HeuristicSearchFast`** (whenever it is applied to the queue of
its own state, which is how the search loop applies it). -/
theorem hsearch_step_expand_sorted_eq_fast (s : hsearch_sorted_state V heur) (head : V)
    (tail : List V) (hst : s.stack = head :: tail) :
    (hsearch_step_expand_sorted G heur s head tail).toFastState
      = hsearch_step_expand_fast G heur s.toFastState head tail := by
  rw [hsearch_step_expand_sorted_eq_core G heur s head tail hst,
    hsearch_expand_sorted_core_toFastState G heur s head tail hst]
  have hitems := hsearch_sorted_items_eq G heur s head tail hst
  have hno : hsearch_sorted_new_order G heur s head
      = fun v => (List.foldl (fun m x => m.insert x.1 x.2.1) s.orderMap
          (hsearch_fast_items G heur s.toFastState head tail)).getD v s.orderDefault := by
    funext v
    unfold hsearch_sorted_new_order hsearch_sorted_orderMap
    rw [hitems]
  unfold hsearch_step_expand_fast
  simp only [hsearch_sorted_stack_eq G heur s head tail hst, hsearch_sorted_newly,
    hsearch_sorted_orderMap, hsearch_sorted_motherMap, hitems, hno]
  rfl

/-- **One expansion step of the sorted search produces exactly the same abstract state as the
reference implementation `hsearch_step_expand`.** -/
theorem hsearch_step_expand_sorted_eq (s : hsearch_sorted_state V heur) (head : V)
    (tail : List V) (hst : s.stack = head :: tail) :
    (hsearch_step_expand_sorted G heur s head tail).toBaseState (g := G.toWeightedDiGraph)
      = hsearch_step_expand (g := G.toWeightedDiGraph) heur
          (s.toBaseState (g := G.toWeightedDiGraph)) head tail := by
  rw [hsearch_sorted_state.toBaseState_eq_toFastState,
    hsearch_step_expand_sorted_eq_fast G heur s head tail hst,
    hsearch_sorted_state.toBaseState_eq_toFastState]
  exact hsearch_step_expand_fast_eq G heur s.toFastState head tail

end

end NatGraph
