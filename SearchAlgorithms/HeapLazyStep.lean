import SearchAlgorithms.HeapLazyQueue

/-!
# One search step of the lazily deleted heap

This module assembles the pieces of `SearchAlgorithms.HeapLazyQueue` into

* `hsearch_lazy_purgeState` — drop the stale entries at the root of the heap (the abstract
  state does not change, `hsearch_lazy_purgeState_toBaseState`);
* `hsearch_expand_lazy_core` — **one expansion**, `O(deg · log m)`, whatever the path orders
  do; this is where the progress line is printed;
* `hsearch_step_expand_lazy` — the expansion as the generic search loop wants it, together
  with `hsearch_step_expand_lazy_eq`: it produces exactly the abstract state of the reference
  implementation;
* `hsearch_lazy_step` / `hsearch_lazy_step_eq` — the step function that reads the next node
  off the heap instead of off the (never built) sorted queue.

## Instrumentation

`hsearch_expand_lazy_core` prints one line on stderr every `traceEvery` expansions, e.g.

```
[search] expanded 100 nodes | queue 3122 | visited 4011 | insertions 7133
```

`traceEvery` is a field of the state, set by `hsearch_lazy_state.initial`; `0` switches the
output off.  Printing is done with `traceIf`, which is the identity function
(`traceIf_eq`), so the traced search is *literally* the same function as the untraced one and
no proof is affected.  To get timestamps, pipe stderr through a tool such as `ts` or
`awk '{ print strftime("%T"), $0 }'`.
-/

namespace NatGraph

open WeightedDiGraph
open SearchAlgorithms

variable {V : Type} [FinEnum V] [BEq V] [LawfulBEq V] [Hashable V]

/-!
## Dropping the stale entries at the root
-/

section

variable (heur : V → ℕ∞)

/-- Drop the stale entries at the root of the heap.  The abstract state does not change —
the entries that are dropped were invisible anyway (`HeapQueue.liveQueue_purge`). -/
def hsearch_lazy_purgeState (s : hsearch_lazy_state V heur) : hsearch_lazy_state V heur where
  vis := s.vis
  orderMap := s.orderMap
  orderDefault := s.orderDefault
  motherMap := s.motherMap
  motherDefault := s.motherDefault
  heap := HeapQueue.purge (hsearch_lazy_key_le heur) (hsearch_lazy_isLive s.queued) s.heap
  queued := s.queued
  nextSeq := s.nextSeq
  expansions := s.expansions
  traceEvery := s.traceEvery
  heap_ordered :=
    HeapQueue.Ordered_purge _ (hsearch_lazy_key_le_trans heur) (hsearch_lazy_key_le_total heur)
      _ s.heap s.heap_ordered
  seq_nodup :=
    HeapQueue.nodup_snd_purge _ (hsearch_lazy_key_le_trans heur)
      (hsearch_lazy_key_le_total heur) _ s.heap s.heap_ordered s.seq_nodup
  seq_lt := fun e he => s.seq_lt e (HeapQueue.mem_of_mem_purge _ (hsearch_lazy_key_le_trans heur)
    (hsearch_lazy_key_le_total heur) _ s.heap s.heap_ordered s.seq_nodup he)
  live_key := fun e he hl => s.live_key e (HeapQueue.mem_of_mem_purge _
    (hsearch_lazy_key_le_trans heur) (hsearch_lazy_key_le_total heur) _ s.heap s.heap_ordered
    s.seq_nodup he) hl
  queued_live := by
    intro v n hv
    obtain ⟨e, he, h1, h2⟩ := s.queued_live v n hv
    refine ⟨e, HeapQueue.mem_purge_of_live _ _ _ he ?_, h1, h2⟩
    rw [hsearch_lazy_isLive_iff, h1, h2, hv]
  queued_visited := s.queued_visited

omit [LawfulBEq V] in
/-- Purging does not change the queue. -/
theorem hsearch_lazy_purgeState_queue (s : hsearch_lazy_state V heur) :
    (hsearch_lazy_purgeState heur s).queue = s.queue := by
  show ((HeapQueue.liveQueue (hsearch_lazy_key_le heur) (hsearch_lazy_isLive s.queued)
    (HeapQueue.purge (hsearch_lazy_key_le heur) (hsearch_lazy_isLive s.queued)
      s.heap)).map Prod.fst) = _
  rw [HeapQueue.liveQueue_purge _ (hsearch_lazy_key_le_trans heur)
    (hsearch_lazy_key_le_total heur) _ s.heap s.heap_ordered s.seq_nodup]
  rfl

omit [LawfulBEq V] in
/-- Purging does not change the flattened state. -/
theorem hsearch_lazy_purgeState_toFastState (s : hsearch_lazy_state V heur) :
    (hsearch_lazy_purgeState heur s).toFastState = s.toFastState := by
  unfold hsearch_lazy_state.toFastState
  rw [hsearch_lazy_purgeState_queue]
  rfl

omit [LawfulBEq V] in
/-- **Purging does not change the abstract state.** -/
theorem hsearch_lazy_purgeState_toBaseState {g : NatGraph V} (s : hsearch_lazy_state V heur) :
    (hsearch_lazy_purgeState heur s).toBaseState (g := g) = s.toBaseState := by
  rw [hsearch_lazy_state.toBaseState_eq_toFastState,
    hsearch_lazy_purgeState_toFastState, hsearch_lazy_state.toBaseState_eq_toFastState]

omit [LawfulBEq V] in
/-- A state whose heap has no root has an empty queue. -/
theorem hsearch_lazy_queue_eq_nil_of_peek_none (s : hsearch_lazy_state V heur)
    (hpk : s.heap.peek = none) : s.queue = [] := by
  show ((HeapQueue.liveQueue (hsearch_lazy_key_le heur) (hsearch_lazy_isLive s.queued)
    s.heap).map Prod.fst) = []
  rw [List.map_eq_nil_iff]
  refine (HeapQueue.liveQueue_eq_nil_iff _ _ _).mpr ?_
  intro e he
  rw [LHeap.peek_eq_none_iff] at hpk
  rw [hpk] at he
  simp at he

omit [LawfulBEq V] in
/-- After purging, the root of the heap is live. -/
theorem hsearch_lazy_purge_peek_live (s : hsearch_lazy_state V heur) (root : LazyEntry V)
    (hpk : (hsearch_lazy_purgeState heur s).heap.peek = some root) :
    hsearch_lazy_isLive (hsearch_lazy_purgeState heur s).queued root = true :=
  HeapQueue.peek_purge_live _ _ _ root hpk

end

/-!
## One expansion
-/

section

variable (G : NatGraphWithGenerator V) (heur : V → ℕ∞)

/-- **One expansion of the search with a lazily deleted heap.**

The heap is popped once and pushed into once per queued or re-queued neighbour; the sorted
queue is never built, and — unlike for the eagerly updated heap of
`SearchAlgorithms.HeuristicSearchHeap` — a decrease-key never rebuilds it either: the entry
that has become obsolete is simply left in the heap as a stale entry.

As in the other implementations the body is spelled out with `let`s so that the per-neighbour
data is computed exactly once and shared, and so that every field of the old state is read
*before* any of its hash maps is updated: a `Std.HashMap` is modified in place only while it
is uniquely referenced, and a reference kept across an update would make every expansion copy
the whole map.  Every field is definitionally the corresponding `hsearch_lazy_*` value, which
is why the six proof fields typecheck.

The state `s` itself must not survive the projections either — it holds a reference to each
of its maps, so anything computed from `s` while `s` is still alive works on a shared map.
That is why the per-neighbour data is computed by `hsearch_lazy_itemsOf`, which takes the
fields, and why the progress line reports the size of the *new* visited set: reading the old
one after the projections would keep it alive across the insertion. -/
def hsearch_expand_lazy_core (s : hsearch_lazy_state V heur) (root : LazyEntry V)
    (hp : s.heap.peek = some root) (hlive : hsearch_lazy_isLive s.queued root = true) :
    hsearch_lazy_state V heur :=
  let head : V := root.1.1
  -- every field of the old state is read first; after this point `s` is dead, so its hash
  -- maps and its visited set are uniquely referenced and are updated in place
  let vis0 := s.vis
  let om := s.orderMap
  let od := s.orderDefault
  let mm := s.motherMap
  let md := s.motherDefault
  let heap0 := s.heap
  let q0 := s.queued
  let ns := s.nextSeq
  let ex := s.expansions
  let te := s.traceEvery
  let qt : Std.HashMap V ℕ := q0.erase head
  let items := hsearch_lazy_itemsOf G heur vis0 om od mm md head qt
  let newly : List V := items.filterMap (fun x => if x.2.2.2 then some x.1 else none)
  let newlyKeys : List (LazyKey V) :=
    items.filterMap (fun x => if x.2.2.2 then some (x.1, x.2.1) else none)
  let changedPairs : List (LazyKey V × LazyEntry V) := items.filterMap (fun x =>
    match qt[x.1]? with
    | none => none
    | some n =>
      if x.2.1 == om.getD x.1 od then none
      else some ((x.1, x.2.1), ((x.1, om.getD x.1 od), n)))
  let changedKeys : List (LazyKey V) :=
    (changedPairs.mergeSort (fun a b => hsearch_lazy_le heur a.2 b.2)).map Prod.fst
  let pushEntries : List (LazyEntry V) := (changedKeys ++ newlyKeys).zipIdx ns
  let newQueued : Std.HashMap V ℕ := pushEntries.foldl (fun m e => m.insert e.1.1 e.2) qt
  let newHeap : LHeap (LazyEntry V) :=
    pushEntries.foldl (LHeap.insert (hsearch_lazy_le heur))
      (LHeap.deleteMin (hsearch_lazy_le heur) heap0)
  let newOrderMap := items.foldl (fun m x => m.insert x.1 x.2.1) om
  let newMotherMap := items.foldl (fun m x => m.insert x.1 x.2.2.1) mm
  let newVis := vis0.insertList newly
  traceIf (te != 0 && (ex + 1) % te == 0)
    (fun _ => s!"[search] expanded {ex + 1} nodes | queue {newQueued.size} | visited {newVis.hashSet.size} | insertions {ns + pushEntries.length}")
  { vis := newVis
    orderMap := newOrderMap
    orderDefault := od
    motherMap := newMotherMap
    motherDefault := md
    heap := newHeap
    queued := newQueued
    nextSeq := ns + pushEntries.length
    expansions := ex + 1
    traceEvery := te
    heap_ordered := by
      show LHeap.Ordered (hsearch_lazy_le heur)
        (hsearch_lazy_newHeap G heur s root.1.1 (s.queued.erase root.1.1))
      exact hsearch_lazy_newHeap_ordered G heur s root.1.1 (s.queued.erase root.1.1)
    seq_nodup := by
      obtain ⟨T, hT⟩ := hsearch_lazy_sorted_eq_cons heur s root hp
      show ((hsearch_lazy_newHeap G heur s root.1.1
        (s.queued.erase root.1.1)).elems.map Prod.snd).Nodup
      exact hsearch_lazy_newHeap_nodup G heur s root T hp hT (s.queued.erase root.1.1)
    seq_lt := by
      obtain ⟨T, hT⟩ := hsearch_lazy_sorted_eq_cons heur s root hp
      show ∀ e ∈ (hsearch_lazy_newHeap G heur s root.1.1 (s.queued.erase root.1.1)).elems,
        e.2 < s.nextSeq
          + (hsearch_lazy_pushEntries G heur s root.1.1 (s.queued.erase root.1.1)).length
      exact hsearch_lazy_newHeap_seq_lt G heur s root T hp hT (s.queued.erase root.1.1)
    live_key := by
      obtain ⟨T, hT⟩ := hsearch_lazy_sorted_eq_cons heur s root hp
      show ∀ e ∈ (hsearch_lazy_newHeap G heur s root.1.1 (s.queued.erase root.1.1)).elems,
        hsearch_lazy_isLive
            (hsearch_lazy_newQueued G heur s root.1.1 (s.queued.erase root.1.1)) e = true →
          e.1.2 = hsearch_lazy_new_order G heur s root.1.1 (s.queued.erase root.1.1) e.1.1
      exact hsearch_lazy_newHeap_live_key G heur s root T hp hlive hT
    queued_live := by
      obtain ⟨T, hT⟩ := hsearch_lazy_sorted_eq_cons heur s root hp
      show ∀ (v : V) (n : ℕ),
        (hsearch_lazy_newQueued G heur s root.1.1 (s.queued.erase root.1.1))[v]? = some n →
        ∃ e ∈ (hsearch_lazy_newHeap G heur s root.1.1 (s.queued.erase root.1.1)).elems,
          e.1.1 = v ∧ e.2 = n
      exact hsearch_lazy_newHeap_queued_live G heur s root T hp hlive hT
    queued_visited := by
      show ∀ v : V, (hsearch_lazy_newQueued G heur s root.1.1
          (s.queued.erase root.1.1)).contains v = true →
        v ∈ (s.vis.insertList (hsearch_lazy_newly G heur s root.1.1
          (s.queued.erase root.1.1))).toFinset
      exact hsearch_lazy_newQueued_visited G heur s root }

/-- The queue after one expansion is the queue of the reference implementation. -/
theorem hsearch_expand_lazy_core_queue (s : hsearch_lazy_state V heur) (root : LazyEntry V)
    (hp : s.heap.peek = some root) (hlive : hsearch_lazy_isLive s.queued root = true)
    (head : V) (tail : List V) (hst : s.queue = head :: tail) (hhead : root.1.1 = head) :
    (hsearch_expand_lazy_core G heur s root hp hlive).queue
      = (tail ++ hsearch_lazy_newly G heur s head (s.queued.erase head)).mergeSort
          (hsearch_queue_le heur
            (hsearch_lazy_new_order G heur s head (s.queued.erase head))) := by
  subst hhead
  obtain ⟨T, hT⟩ := hsearch_lazy_sorted_eq_cons heur s root hp
  have hq := hsearch_lazy_queue_cons heur s root T hlive hT
  rw [hst] at hq
  have htail : tail = hsearch_lazy_tail heur s T := (List.cons.inj hq).2
  subst htail
  show (hsearch_expand_lazy_core G heur s root hp hlive).queue = _
  unfold hsearch_expand_lazy_core
  rw [traceIf_eq]
  exact hsearch_lazy_newHeap_liveQueue G heur s root T hp hlive hT

/-- The fields of the expansion are the `hsearch_lazy_*` values (the `let`s only make the
computation share its intermediate results, and `traceIf` is the identity). -/
theorem hsearch_expand_lazy_core_toFastState (s : hsearch_lazy_state V heur)
    (root : LazyEntry V) (hp : s.heap.peek = some root)
    (hlive : hsearch_lazy_isLive s.queued root = true)
    (head : V) (tail : List V) (hst : s.queue = head :: tail) (hhead : root.1.1 = head) :
    (hsearch_expand_lazy_core G heur s root hp hlive).toFastState
      = { vis := s.vis.insertList (hsearch_lazy_newly G heur s head (s.queued.erase head))
          orderMap := hsearch_lazy_orderMap G heur s head (s.queued.erase head)
          orderDefault := s.orderDefault
          motherMap := hsearch_lazy_motherMap G heur s head (s.queued.erase head)
          motherDefault := s.motherDefault
          stack := (tail ++ hsearch_lazy_newly G heur s head (s.queued.erase head)).mergeSort
            (hsearch_queue_le heur
              (hsearch_lazy_new_order G heur s head (s.queued.erase head))) } := by
  rw [← hsearch_expand_lazy_core_queue G heur s root hp hlive head tail hst hhead]
  subst hhead
  show (hsearch_expand_lazy_core G heur s root hp hlive).toFastState = _
  unfold hsearch_expand_lazy_core
  rw [traceIf_eq]
  rfl

/-- **One expansion produces exactly the same flattened state as the fast search of
`SearchAlgorithms.HeuristicSearchFast`.** -/
theorem hsearch_expand_lazy_core_eq_fast (s : hsearch_lazy_state V heur) (root : LazyEntry V)
    (hp : s.heap.peek = some root) (hlive : hsearch_lazy_isLive s.queued root = true)
    (head : V) (tail : List V) (hst : s.queue = head :: tail) (hhead : root.1.1 = head) :
    (hsearch_expand_lazy_core G heur s root hp hlive).toFastState
      = hsearch_step_expand_fast G heur s.toFastState head tail := by
  rw [hsearch_expand_lazy_core_toFastState G heur s root hp hlive head tail hst hhead]
  subst hhead
  obtain ⟨T, hT⟩ := hsearch_lazy_sorted_eq_cons heur s root hp
  have hq := hsearch_lazy_queue_cons heur s root T hlive hT
  rw [hst] at hq
  have htail : tail = hsearch_lazy_tail heur s T := (List.cons.inj hq).2
  subst htail
  have hitems := hsearch_lazy_items_eq G heur s root T hp hlive hT
  have hno : hsearch_lazy_new_order G heur s root.1.1 (s.queued.erase root.1.1)
      = fun v => (List.foldl (fun m x => m.insert x.1 x.2.1) s.orderMap
          (hsearch_fast_items G heur s.toFastState root.1.1
            (hsearch_lazy_tail heur s T))).getD v s.orderDefault := by
    funext v
    unfold hsearch_lazy_new_order hsearch_lazy_orderMap
    rw [hitems]
  unfold hsearch_step_expand_fast
  simp only [hsearch_lazy_newly, hsearch_lazy_orderMap, hsearch_lazy_motherMap, hitems, hno]
  rfl

/-!
## The expansion step of the search loop
-/

/-- Expand the root of an already purged heap. -/
def hsearch_expand_lazy_purged (s : hsearch_lazy_state V heur)
    (hlv : ∀ root, s.heap.peek = some root → hsearch_lazy_isLive s.queued root = true) :
    hsearch_lazy_state V heur :=
  match hpk : s.heap.peek with
  | none => s
  | some root => hsearch_expand_lazy_core G heur s root hpk (hlv root hpk)

/-- One expansion step of the lazy heap search: purge the stale entries at the root, then
expand the root.  The arguments `_head` and `_tail` (which the generic search loop passes)
are ignored — the node to expand is read off the heap. -/
def hsearch_step_expand_lazy (s : hsearch_lazy_state V heur) (_head : V) (_tail : List V) :
    hsearch_lazy_state V heur :=
  hsearch_expand_lazy_purged G heur (hsearch_lazy_purgeState heur s)
    (fun root hpk => hsearch_lazy_purge_peek_live heur s root hpk)

/-- Whenever the purged heap is non-empty, the expansion step is
`hsearch_expand_lazy_core`. -/
theorem hsearch_step_expand_lazy_eq_core (s : hsearch_lazy_state V heur) (root : LazyEntry V)
    (hpk : (hsearch_lazy_purgeState heur s).heap.peek = some root) (head : V) (tail : List V) :
    hsearch_step_expand_lazy G heur s head tail
      = hsearch_expand_lazy_core G heur (hsearch_lazy_purgeState heur s) root hpk
          (hsearch_lazy_purge_peek_live heur s root hpk) := by
  unfold hsearch_step_expand_lazy hsearch_expand_lazy_purged
  split
  · next h => rw [h] at hpk; exact absurd hpk (by simp)
  · next root' h =>
    rw [h] at hpk
    obtain rfl : root' = root := Option.some.inj hpk
    rfl

omit [LawfulBEq V] in
/-- Whenever the queue is non-empty, the purged heap has a root, and it is the head of the
queue. -/
theorem hsearch_lazy_purge_peek_head (s : hsearch_lazy_state V heur) (head : V)
    (tail : List V) (hst : s.queue = head :: tail) :
    ∃ root : LazyEntry V,
      (hsearch_lazy_purgeState heur s).heap.peek = some root ∧ root.1.1 = head := by
  rcases hpk : (hsearch_lazy_purgeState heur s).heap.peek with _ | root
  · exfalso
    have hnil := hsearch_lazy_queue_eq_nil_of_peek_none heur (hsearch_lazy_purgeState heur s) hpk
    rw [hsearch_lazy_purgeState_queue, hst] at hnil
    exact absurd hnil (by simp)
  · refine ⟨root, rfl, ?_⟩
    obtain ⟨T, hT⟩ := hsearch_lazy_sorted_eq_cons heur (hsearch_lazy_purgeState heur s) root hpk
    have hq := hsearch_lazy_queue_cons heur (hsearch_lazy_purgeState heur s) root T
      (hsearch_lazy_purge_peek_live heur s root hpk) hT
    rw [hsearch_lazy_purgeState_queue, hst] at hq
    exact ((List.cons.inj hq).1).symm

/-- **One expansion step of the lazy heap search produces exactly the same flattened state as
the fast search of `SearchAlgorithms.HeuristicSearchFast`** (whenever it is applied to the
queue of its own state, which is how the search loop applies it). -/
theorem hsearch_step_expand_lazy_eq_fast (s : hsearch_lazy_state V heur) (head : V)
    (tail : List V) (hst : s.queue = head :: tail) :
    (hsearch_step_expand_lazy G heur s head tail).toFastState
      = hsearch_step_expand_fast G heur s.toFastState head tail := by
  obtain ⟨root, hpk, hhead⟩ := hsearch_lazy_purge_peek_head heur s head tail hst
  rw [hsearch_step_expand_lazy_eq_core G heur s root hpk head tail,
    hsearch_expand_lazy_core_eq_fast G heur (hsearch_lazy_purgeState heur s) root hpk
      (hsearch_lazy_purge_peek_live heur s root hpk) head tail
      (by rw [hsearch_lazy_purgeState_queue]; exact hst) hhead,
    hsearch_lazy_purgeState_toFastState]

/-- **One expansion step of the lazy heap search produces exactly the same abstract state as
the reference implementation `hsearch_step_expand`.** -/
theorem hsearch_step_expand_lazy_eq (s : hsearch_lazy_state V heur) (head : V)
    (tail : List V) (hst : s.queue = head :: tail) :
    (hsearch_step_expand_lazy G heur s head tail).toBaseState (g := G.toWeightedDiGraph)
      = hsearch_step_expand (g := G.toWeightedDiGraph) heur
          (s.toBaseState (g := G.toWeightedDiGraph)) head tail := by
  rw [hsearch_lazy_state.toBaseState_eq_toFastState,
    hsearch_step_expand_lazy_eq_fast G heur s head tail hst,
    hsearch_lazy_state.toBaseState_eq_toFastState]
  exact hsearch_step_expand_fast_eq G heur s.toFastState head tail

/-!
## The step function of the search loop
-/

/-- **The step function of the lazy heap search.**  It reads the next node to expand off the
heap (amortised `O(log m)`, counting the stale entries it drops on the way) instead of off
the abstract queue, which would have to be sorted first. -/
def hsearch_lazy_step :
    search_step_function (G.toWeightedDiGraph) (ℕ × ℕ) (hsearch_lazy_state V heur) :=
  fun goal s =>
    match hpk : (hsearch_lazy_purgeState heur s).heap.peek with
    | none => (s, some false)
    | some root =>
      if root.1.1 = goal then (s, some true)
      else
        (hsearch_expand_lazy_core G heur (hsearch_lazy_purgeState heur s) root hpk
          (hsearch_lazy_purge_peek_live heur s root hpk), none)

/-- **Popping the heap is the same step as taking the head of the abstract queue.**  This is
the equation that `WeightedDiGraph.search_exe_with_step_eq` needs: everything that is known
about the ordinary search loop applies to the lazy heap search verbatim. -/
theorem hsearch_lazy_step_eq :
    hsearch_lazy_step G heur
      = search_stack_step (G := G.toWeightedDiGraph) (D := ℕ × ℕ)
          (state_type := hsearch_lazy_state V heur) (hsearch_step_expand_lazy G heur) := by
  funext goal s
  unfold hsearch_lazy_step search_stack_step
  split
  · next hpk =>
    have hq : (has_base_search_state.to_base_state (G := G.toWeightedDiGraph) (D := ℕ × ℕ)
        (B := hsearch_lazy_state V heur) s).stack = [] := by
      show s.queue = []
      rw [← hsearch_lazy_purgeState_queue heur s]
      exact hsearch_lazy_queue_eq_nil_of_peek_none heur (hsearch_lazy_purgeState heur s) hpk
    simp only [hq]
  · next root hpk =>
    have hq : (has_base_search_state.to_base_state (G := G.toWeightedDiGraph) (D := ℕ × ℕ)
        (B := hsearch_lazy_state V heur) s).stack = root.1.1 :: s.queue.tail := by
      show s.queue = root.1.1 :: s.queue.tail
      obtain ⟨T, hT⟩ := hsearch_lazy_sorted_eq_cons heur (hsearch_lazy_purgeState heur s) root hpk
      have h := hsearch_lazy_queue_cons heur (hsearch_lazy_purgeState heur s) root T
        (hsearch_lazy_purge_peek_live heur s root hpk) hT
      rw [hsearch_lazy_purgeState_queue] at h
      rw [h]
      simp
    simp only [hq]
    split
    · rfl
    · rw [hsearch_step_expand_lazy_eq_core G heur s root hpk]

end

end NatGraph
