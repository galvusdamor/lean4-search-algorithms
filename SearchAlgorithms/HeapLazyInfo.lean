import SearchAlgorithms.HeapLazyBucket

/-!
# The bucket queue search with one map for path orders and mothers

`astar_bq_fastpath` keeps the two maps of the stored search: path orders and mothers, and
updates both for every neighbour of an expanded vertex — also for the many neighbours whose
entries do not change.  This search keeps **one** map `info` from a vertex to its path order
and mother, reads both with one lookup, and writes it only for the neighbours whose entries
change.

Its states are related to the stored states (`BIRel`) like those of the bucket queue search,
except that `info` is related to the two maps only **through their lookups**: for every vertex,
`info` gives the path order and the mother that the two maps give.  That is all the search
reads from them, so the relation is preserved by every step, and the search returns the same
path as `astar_heap_stored_fastpath` (`astar_bi_fastpath_eq_stored`).
-/

namespace NatGraph

open WeightedDiGraph
open SearchAlgorithms

variable {V : Type} [FinEnum V] [BEq V] [LawfulBEq V] [Hashable V]

/-- The data of a state: that of a bucket queue state, with one map for path orders and
mothers. -/
structure hsearch_bi_data (V : Type) [BEq V] [Hashable V] [FinEnum V] (heur : V → ℕ∞) where
  vis : VisitedSet V
  info : Std.HashMap V ((ℕ × ℕ) × V)
  orderDefault : ℕ × ℕ
  motherDefault : V
  queue : RQ (StoredEntry V)
  queued : Std.HashMap V ℕ
  nextSeq : ℕ
  expansions : ℕ
  traceEvery : ℕ

variable {heur : V → ℕ∞}

/-- **The relation to a stored state.** -/
structure BIRel (d : hsearch_bi_data V heur) (s : hsearch_stored_state V heur) : Prop where
  vis : d.vis = s.vis
  od : d.orderDefault = s.orderDefault
  md : d.motherDefault = s.motherDefault
  info : ∀ v, d.info.getD v (s.orderDefault, s.motherDefault)
    = (s.orderMap.getD v s.orderDefault, s.motherMap.getD v s.motherDefault)
  queued : d.queued = s.queued
  ns : d.nextSeq = s.nextSeq
  ex : d.expansions = s.expansions
  te : d.traceEvery = s.traceEvery
  wf : RQ.WF bkey bidx d.queue
  elems : RQ.elems d.queue = HeapQueue.sortedList storedKeyLe s.heap

/-- A state: data related to a stored state. -/
def hsearch_bi_state (V : Type) [BEq V] [LawfulBEq V] [Hashable V] [FinEnum V]
    (heur : V → ℕ∞) : Type :=
  {d : hsearch_bi_data V heur // ∃ s, BIRel d s}

/-- Drop the stale entries at the front of the queue. -/
def biPurge (d : hsearch_bi_data V heur) : hsearch_bi_data V heur :=
  { d with queue := purgeQ (storedIsLive d.queued) d.queue }

omit [LawfulBEq V] in
theorem biPurge_rel {d : hsearch_bi_data V heur} {s : hsearch_stored_state V heur}
    (h : BIRel d s) : BIRel (biPurge d) (hsearch_stored_purgeState heur s) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, hwf, he⟩ := h
  obtain ⟨w1, w2⟩ := purgeQ_spec (storedIsLive d.queued) d.queue hwf
  refine ⟨h1, h2, h3, h4, h5, h6, h7, h8, w1, ?_⟩
  show RQ.elems (purgeQ (storedIsLive d.queued) d.queue) = HeapQueue.sortedList storedKeyLe
    (HeapQueue.purge storedKeyLe (storedIsLive s.queued) s.heap)
  rw [w2, he, h5, sortedList_purge _ s.heap (stored_ordered s) (stored_nodup s)]

omit [LawfulBEq V] in
theorem bi_peek_eq {d : hsearch_bi_data V heur} {s : hsearch_stored_state V heur}
    (h : BIRel d s) : d.queue.peek = s.heap.peek := by
  rw [RQ.peek_eq h.wf, h.elems, stored_peek_eq]

/-! ### The neighbours of an expanded vertex -/

omit [FinEnum V] [BEq V] [LawfulBEq V] [Hashable V] in
theorem flatMap_coe_eq {β : Type} (p : Finset β) (l : List ↥p) :
    l.flatMap (fun a => [a.val]) = l.map Subtype.val := by
  induction l <;> simp_all

/-- The data of one neighbour of an expanded vertex. -/
structure BItem (V : Type) where
  v : V
  no : ℕ × ℕ
  nm : V
  isNew : Bool
  ht : Thunk ℕ∞
  changed : Bool
  vo : ℕ × ℕ

/-- The data in the form of `hsearch_stored_itemsOf`. -/
@[inline] def BItem.toStored {V : Type} (x : BItem V) : (V × ((ℕ × ℕ) × V × Bool)) × Thunk ℕ∞ :=
  ((x.v, x.no, x.nm, x.isNew), x.ht)

section

variable (G : NatGraphWithGenerator V) (heur : V → ℕ∞)

/-- The per-neighbour data of `hsearch_stored_itemsOfFast` in one record, with two more
components: whether the entry of the neighbour changes, and its old path order. -/
def biItemsOf (vis : VisitedSet V) (info : Std.HashMap V ((ℕ × ℕ) × V)) (od : ℕ × ℕ) (md : V)
    (hd : V) (qm : Std.HashMap V ℕ) : List (BItem V) :=
  let hdo : ℕ × ℕ := (info.getD hd (od, md)).1
  (G.neighboursE hd).map (fun x =>
    let v : V := x.1
    let c : ℕ := x.2
    let pv : ℕ × ℕ := ⟨hdo.fst + c, hdo.snd + 1⟩
    let isVisited : Bool := vis.hashSet.contains v
    let vi : (ℕ × ℕ) × V := info.getD v (od, md)
    let vo : ℕ × ℕ := vi.1
    let no : ℕ × ℕ :=
      if isVisited then
        (if vo.1 < pv.1 then vo else if vo.1 = pv.1 ∧ vo.2 < pv.2 then vo else pv)
      else pv
    let nm : V :=
      if isVisited then
        (if vo = no then vi.2 else hd)
      else hd
    let ht : Thunk ℕ∞ := Thunk.mk (fun _ => heur v)
    let isNew : Bool :=
      (!isVisited || (decide (vo.fst > hdo.fst + c) && (!qm.contains v))) &&
        decide (ht.get ≠ ⊤)
    ⟨v, no, nm, isNew, ht, !isVisited || no != vo, vo⟩)

omit [LawfulBEq V] in
theorem biItemsOf_map (vis : VisitedSet V) (info : Std.HashMap V ((ℕ × ℕ) × V))
    (om : Std.HashMap V (ℕ × ℕ)) (od : ℕ × ℕ) (mm : Std.HashMap V V) (md : V)
    (hinfo : ∀ v, info.getD v (od, md) = (om.getD v od, mm.getD v md)) (hd : V)
    (qm : Std.HashMap V ℕ) :
    (biItemsOf G heur vis info od md hd qm).map BItem.toStored
      = hsearch_stored_itemsOf G heur vis om od mm md hd qm := by
  rw [hsearch_stored_itemsOf_eq_fast]
  unfold biItemsOf hsearch_stored_itemsOfFast
  rw [List.map_map]
  refine List.map_congr_left (fun x _ => ?_)
  simp only [Function.comp_apply, BItem.toStored, hinfo]

omit [LawfulBEq V] in
theorem biItemsOf_spec (vis : VisitedSet V) (info : Std.HashMap V ((ℕ × ℕ) × V))
    (od : ℕ × ℕ) (md : V) (hd : V) (qm : Std.HashMap V ℕ) :
    ∀ x ∈ biItemsOf G heur vis info od md hd qm,
      x.vo = (info.getD x.v (od, md)).1 ∧
        (x.changed = false → x.no = (info.getD x.v (od, md)).1 ∧
          x.nm = (info.getD x.v (od, md)).2) := by
  intro x hx
  unfold biItemsOf at hx
  obtain ⟨y, -, rfl⟩ := List.mem_map.1 hx
  refine ⟨rfl, ?_⟩
  intro hc
  simp only [Bool.or_eq_false_iff, Bool.not_eq_false', bne_eq_false_iff_eq] at hc
  obtain ⟨hv, hno⟩ := hc
  simp only [hv, if_true] at hno ⊢
  refine ⟨hno, ?_⟩
  rw [if_pos hno.symm]

omit [LawfulBEq V] in
/-- The keys of the per-neighbour data are distinct. -/
theorem biItemsOf_nodup (vis : VisitedSet V) (info : Std.HashMap V ((ℕ × ℕ) × V))
    (od : ℕ × ℕ) (md : V) (hd : V) (qm : Std.HashMap V ℕ) :
    ((biItemsOf G heur vis info od md hd qm).map (fun x => x.v)).Nodup := by
  unfold biItemsOf
  rw [List.map_map]
  have : ((G.neighboursE hd).map Prod.fst).Nodup := by
    rw [G.neighboursE_eq, List.map_map]
    simp only [Function.comp_def, List.map_subtype, List.unattach_attach, List.map_id']
    refine (G.neighbours_sublist hd).nodup ?_
    have := (FinEnum.nodup_toList (α := ↥(Finset.univ : Finset V))).map
      (f := Subtype.val) (fun a b h => Subtype.ext h)
    change (List.flatMap (fun a : ↥(Finset.univ : Finset V) => [(a : V)]) _).Nodup
    rw [flatMap_coe_eq]
    exact this
  exact this

end

omit [FinEnum V] in
/-- Updating `info` only for the changed entries gives the lookups of updating both maps for
all entries. -/
theorem info_foldl {α : Type} (key : α → V) (no : α → ℕ × ℕ) (nm : α → V) (ch : α → Bool) :
    ∀ (l : List α) (info : Std.HashMap V ((ℕ × ℕ) × V)) (om : Std.HashMap V (ℕ × ℕ))
      (mm : Std.HashMap V V) (od : ℕ × ℕ) (md : V), (l.map key).Nodup →
      (∀ v, info.getD v (od, md) = (om.getD v od, mm.getD v md)) →
      (∀ x ∈ l, ch x = false → no x = om.getD (key x) od ∧ nm x = mm.getD (key x) md) →
      ∀ v, (l.foldl (fun m x => if ch x then m.insert (key x) (no x, nm x) else m) info).getD
          v (od, md)
        = ((l.foldl (fun m x => m.insert (key x) (no x)) om).getD v od,
           (l.foldl (fun m x => m.insert (key x) (nm x)) mm).getD v md)
  | [], info, om, mm, od, md, _, hinv, _ => hinv
  | y :: l, info, om, mm, od, md, hnd, hinv, hun => by
    rw [List.map_cons, List.nodup_cons] at hnd
    simp only [List.foldl_cons]
    apply info_foldl key no nm ch l _ _ _ od md hnd.2
    · intro v
      split
      · rw [Std.HashMap.getD_insert, Std.HashMap.getD_insert, Std.HashMap.getD_insert]
        split
        · rfl
        · exact hinv v
      · next hc =>
        obtain ⟨h1, h2⟩ := hun y List.mem_cons_self (by simpa using hc)
        rw [Std.HashMap.getD_insert, Std.HashMap.getD_insert]
        split
        · next hk =>
          have hk' : key y = v := by simpa using hk
          subst hk'
          rw [hinv, h1, h2]
        · exact hinv v
    · intro x hx hc
      obtain ⟨h1, h2⟩ := hun x (List.mem_cons_of_mem _ hx) hc
      have hne : ¬ (key y == key x) = true := by
        simp only [beq_iff_eq]
        intro he
        exact hnd.1 (he ▸ List.mem_map_of_mem hx)
      rw [Std.HashMap.getD_insert, Std.HashMap.getD_insert, if_neg hne, if_neg hne]
      exact ⟨h1, h2⟩


/-! ### One expansion -/

section

variable (G : NatGraphWithGenerator V) (heur : V → ℕ∞)

/-- **One expansion** with one map for path orders and mothers. -/
def biCore (d : hsearch_bi_data V heur) (root : StoredEntry V) : hsearch_bi_data V heur :=
  let head : V := root.1.1.1
  let vis0 := d.vis
  let info := d.info
  let od := d.orderDefault
  let md := d.motherDefault
  let heap0 := d.queue
  let q0 := d.queued
  let ns := d.nextSeq
  let ex := d.expansions
  let te := d.traceEvery
  let qt : Std.HashMap V ℕ := q0.erase head
  let items := biItemsOf G heur vis0 info od md head qt
  let newly : List V := items.filterMap (fun x => if x.isNew then some x.v else none)
  let newlyKeys : List (StoredKey V) := items.filterMap
    (fun x => if x.isNew then some ((x.v, x.no), addH x.no x.ht.get) else none)
  let changedPairs : List (StoredKey V × StoredEntry V) := items.filterMap (fun x =>
    if x.changed then
      match qt[x.v]? with
      | none => none
      | some n =>
        let ov := x.vo
        if x.no == ov then none
        else
          let hv := x.ht.get
          some (((x.v, x.no), addH x.no hv), (((x.v, ov), addH ov hv), n))
    else none)
  let changedKeys : List (StoredKey V) :=
    (changedPairs.mergeSort (fun a b => storedLe a.2 b.2)).map Prod.fst
  let pushEntries : List (StoredEntry V) := (changedKeys ++ newlyKeys).zipIdx ns
  let newQueued : Std.HashMap V ℕ := pushEntries.foldl (fun m e => m.insert e.1.1.1 e.2) qt
  let newHeap : RQ (StoredEntry V) := RQ.insertAll bkey (RQ.pop heap0) pushEntries
  let newInfo := items.foldl
    (fun m x => if x.changed then m.insert x.v (x.no, x.nm) else m) info
  let newVis := vis0.insertList newly
  traceIf (te != 0 && (ex + 1) % te == 0)
    (fun _ => s!"[search] expanded {ex + 1} nodes | queue {newQueued.size} | visited {newVis.hashSet.size} | insertions {ns + pushEntries.length}")
  { vis := newVis
    info := newInfo
    orderDefault := od
    motherDefault := md
    queue := newHeap
    queued := newQueued
    nextSeq := ns + pushEntries.length
    expansions := ex + 1
    traceEvery := te }

theorem stored_core_fields (s : hsearch_stored_state V heur) (root : StoredEntry V)
    (hp : s.heap.peek = some root)
    (hlive : hsearch_lazy_isLive s.queued (eraseEntry root) = true) :
    let c := hsearch_stored_core G heur s root hp hlive
    let qt := s.queued.erase root.1.1.1
    c.vis = s.vis.insertList (hsearch_stored_newly G heur s root.1.1.1 qt) ∧
    c.orderMap = hsearch_stored_orderMap G heur s root.1.1.1 qt ∧
    c.orderDefault = s.orderDefault ∧
    c.motherMap = hsearch_stored_motherMap G heur s root.1.1.1 qt ∧
    c.motherDefault = s.motherDefault ∧
    c.queued = hsearch_stored_newQueued G heur s root.1.1.1 qt ∧
    c.nextSeq = s.nextSeq + (hsearch_stored_pushEntries G heur s root.1.1.1 qt).length ∧
    c.expansions = s.expansions + 1 ∧ c.traceEvery = s.traceEvery := by
  unfold hsearch_stored_core
  simp only [traceIf_eq]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> first | rfl | trivial

/-- **One expansion preserves the relation.** -/
theorem biCore_rel {d : hsearch_bi_data V heur} {s : hsearch_stored_state V heur}
    (h : BIRel d s) (root : StoredEntry V) (hp : s.heap.peek = some root)
    (hlive : hsearch_lazy_isLive s.queued (eraseEntry root) = true) :
    BIRel (biCore G heur d root) (hsearch_stored_core G heur s root hp hlive) := by
  obtain ⟨vis, info, od, md, q, qd, ns, ex, te⟩ := d
  obtain ⟨hv, hod, hmd, hinfo, hq, hns, hex, hte, hwf, he⟩ := h
  simp only at hv hod hmd hinfo hq hns hex hte hwf he
  subst hv hod hmd hq hns hex hte
  set qt := s.queued.erase root.1.1.1 with hqt
  set I2 := biItemsOf G heur s.vis info s.orderDefault s.motherDefault root.1.1.1 qt with hI2
  have hI : I2.map BItem.toStored = hsearch_stored_items G heur s root.1.1.1 qt :=
    biItemsOf_map G heur s.vis info s.orderMap s.orderDefault s.motherMap s.motherDefault hinfo
      root.1.1.1 qt
  have hspec := biItemsOf_spec G heur s.vis info s.orderDefault s.motherDefault root.1.1.1 qt
  have hnewly : I2.filterMap (fun x => if x.isNew then some x.v else none)
      = hsearch_stored_newly G heur s root.1.1.1 qt := by
    unfold hsearch_stored_newly; rw [← hI, List.filterMap_map]; rfl
  have hnewlyKeys : I2.filterMap (fun x => if x.isNew then
        some ((x.v, x.no), addH x.no x.ht.get) else none)
      = hsearch_stored_newlyKeys G heur s root.1.1.1 qt := by
    unfold hsearch_stored_newlyKeys; rw [← hI, List.filterMap_map]; rfl
  have hchanged : I2.filterMap (fun x =>
      if x.changed then
        match qt[x.v]? with
        | none => none
        | some n =>
          if x.no == x.vo then none
          else some (((x.v, x.no), addH x.no x.ht.get),
            (((x.v, x.vo), addH x.vo x.ht.get), n))
      else none) = hsearch_stored_changedPairs G heur s root.1.1.1 qt := by
    unfold hsearch_stored_changedPairs
    rw [← hI, List.filterMap_map]
    apply List.filterMap_congr
    intro x hx
    obtain ⟨h1, h2⟩ := hspec x hx
    have hov : x.vo = s.orderMap.getD x.v s.orderDefault := by rw [h1, hinfo]
    simp only [Function.comp_apply, BItem.toStored]
    cases hc : x.changed with
    | false =>
      obtain ⟨h3, -⟩ := h2 hc
      rw [hinfo] at h3
      simp only [Bool.false_eq_true, if_false]
      split
      · rfl
      · rw [if_pos (by simp [h3])]
    | true =>
      simp only [if_true]
      rw [hov]
      cases qt[x.v]? <;> rfl
  have hpush : ((I2.filterMap (fun x =>
      if x.changed then
        match qt[x.v]? with
        | none => none
        | some n =>
          if x.no == x.vo then none
          else some (((x.v, x.no), addH x.no x.ht.get),
            (((x.v, x.vo), addH x.vo x.ht.get), n))
      else none)).mergeSort (fun a b => storedLe a.2 b.2)).map Prod.fst ++
      I2.filterMap (fun x => if x.isNew then
        some ((x.v, x.no), addH x.no x.ht.get) else none)
      = hsearch_stored_changedKeys G heur s root.1.1.1 qt
        ++ hsearch_stored_newlyKeys G heur s root.1.1.1 qt := by
    rw [hchanged, hnewlyKeys]; rfl
  obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8, f9⟩ := stored_core_fields G heur s root hp hlive
  have hcore : biCore G heur ⟨s.vis, info, s.orderDefault, s.motherDefault, q, s.queued,
        s.nextSeq, s.expansions, s.traceEvery⟩ root
      = ⟨s.vis.insertList (hsearch_stored_newly G heur s root.1.1.1 qt),
         I2.foldl (fun m x => if x.changed then m.insert x.v (x.no, x.nm) else m) info,
         s.orderDefault, s.motherDefault,
         RQ.insertAll bkey (RQ.pop q) (hsearch_stored_pushEntries G heur s root.1.1.1 qt),
         hsearch_stored_newQueued G heur s root.1.1.1 qt,
         s.nextSeq + (hsearch_stored_pushEntries G heur s root.1.1.1 qt).length,
         s.expansions + 1, s.traceEvery⟩ := by
    unfold biCore
    simp only [traceIf_eq]
    rw [hnewly]
    unfold hsearch_stored_newQueued hsearch_stored_pushEntries
    rw [← hpush]
  rw [hcore]
  have hlt : ∀ x ∈ RQ.elems (RQ.pop q),
      ∀ y ∈ hsearch_stored_pushEntries G heur s root.1.1.1 qt, bidx x < bidx y := by
    intro x hx y hy
    rw [RQ.elems_pop hwf] at hx
    have hx' : x ∈ s.heap.elems := by
      have := List.mem_of_mem_tail hx
      rw [he] at this
      exact (HeapQueue.sortedList_perm storedKeyLe s.heap).mem_iff.mp this
    exact Nat.lt_of_lt_of_le (stored_seq_lt s x hx') (mem_zipIdx_ge _ _ y hy)
  obtain ⟨hperm, hwf'⟩ := RQ.elems_insertAll_WF _ (RQ.pop q) (RQ.WF_pop hwf) hlt
    (pairwise_zipIdx _ _)
  refine ⟨f1.symm, f3.symm, f5.symm, ?_, f6.symm, f7.symm, f8.symm, f9.symm, hwf', ?_⟩
  · intro v
    rw [f2, f3, f4, f5]
    unfold hsearch_stored_orderMap hsearch_stored_motherMap
    rw [← hI, List.foldl_map, List.foldl_map]
    refine info_foldl (fun x => x.v) (fun x => x.no) (fun x => x.nm)
      (fun x => x.changed) I2 info s.orderMap s.motherMap s.orderDefault s.motherDefault
      (biItemsOf_nodup G heur _ _ _ _ _ _) hinfo ?_ v
    intro x hx hc
    obtain ⟨-, h2⟩ := hspec x hx
    obtain ⟨h3, h4⟩ := h2 hc
    rw [hinfo] at h3 h4
    exact ⟨h3, h4⟩
  · rw [stored_core_heap]
    obtain ⟨t, ht⟩ := HeapQueue.sortedList_head storedKeyLe storedKeyLe_trans storedKeyLe_total
      s.heap root (stored_ordered s) (stored_nodup s) hp
    have hdel : (LHeap.deleteMin storedLe s.heap).elems.Perm t := by
      have h1 := LHeap.elems_deleteMin storedLe s.heap root hp
      have h2 : s.heap.elems.Perm (root :: t) :=
        (HeapQueue.sortedList_perm storedKeyLe s.heap).symm.trans (by rw [ht])
      exact List.Perm.cons_inv (h1.symm.trans h2)
    refine bq_eq_sortedList _ _ hwf' ?_ ?_
    · refine hperm.trans ?_
      rw [RQ.elems_pop hwf, he, ht, List.tail_cons]
      refine List.Perm.trans ?_ (LHeap.elems_insertAll storedLe _ _).symm
      exact hdel.symm.append_right _
    · have := stored_nodup (hsearch_stored_core G heur s root hp hlive)
      rwa [stored_core_heap] at this

end


section

variable (G : NatGraphWithGenerator V) (heur : V → ℕ∞)

/-- One expansion step: purge, then expand the root. -/
def biExpand (d : hsearch_bi_data V heur) : hsearch_bi_data V heur :=
  match (biPurge d).queue.peek with
  | none => biPurge d
  | some root => biCore G heur (biPurge d) root

theorem biExpand_rel {d : hsearch_bi_data V heur} {s : hsearch_stored_state V heur}
    (h : BIRel d s) (head : V) (tail : List V) :
    BIRel (biExpand G heur d) (hsearch_step_expand_stored G heur s head tail) := by
  have hpr := biPurge_rel h
  have hpk := bi_peek_eq hpr
  unfold biExpand hsearch_step_expand_stored
  cases hq : (biPurge d).queue.peek with
  | none =>
    have hs : (hsearch_stored_purgeState heur s).heap.peek = none := by rw [← hpk, hq]
    dsimp only
    split
    · exact hpr
    · rename_i r hr; rw [hs] at hr; cases hr
  | some root =>
    have hs : (hsearch_stored_purgeState heur s).heap.peek = some root := by rw [← hpk, hq]
    dsimp only
    split
    · rename_i hr; rw [hs] at hr; cases hr
    · rename_i r hr
      rw [hs] at hr
      cases hr
      exact biCore_rel G heur hpr root _ _

end

/-! ### The abstract state -/

section

variable {heur : V → ℕ∞}

@[reducible]
def biToBase {g : NatGraph V} (d : hsearch_bi_data V heur) : hsearch_search_state g where
  visited := d.vis.toFinset
  pathOrder := fun v => (d.info.getD v (d.orderDefault, d.motherDefault)).1
  mother := fun x => (d.info.getD x.1 (d.orderDefault, d.motherDefault)).2
  stack := ((RQ.elems d.queue).filter (storedIsLive d.queued)).map (fun e => e.1.1.1)

omit [LawfulBEq V] in
theorem biToBase_eq {g : NatGraph V} {d : hsearch_bi_data V heur}
    {s : hsearch_stored_state V heur} (h : BIRel d s) : biToBase (g := g) d = s.toBaseState := by
  unfold biToBase hsearch_stored_state.toBaseState hsearch_stored_state.storedQueue
  rw [h.vis, h.od, h.md, h.elems, h.queued]
  congr 1
  · funext v; rw [h.info]
  · funext x; rw [h.info]

instance instHasBaseSearchStateBI (g : NatGraph V) (heur : V → ℕ∞) :
    WeightedDiGraph.has_base_search_state g (ℕ × ℕ) (hsearch_bi_state V heur) where
  to_base_state := fun s => biToBase s.1

theorem bi_to_base {g : NatGraph V} (s : hsearch_bi_state V heur)
    {st : hsearch_stored_state V heur} (h : BIRel s.1 st) :
    has_base_search_state.to_base_state (G := g) (D := ℕ × ℕ) s
      = has_base_search_state.to_base_state (G := g) (D := ℕ × ℕ) st :=
  biToBase_eq h

end

/-! ### The search -/

section

variable (G : NatGraphWithGenerator V) (heur : V → ℕ∞)

def hsearch_step_expand_bi (s : hsearch_bi_state V heur) (_head : V) (_tail : List V) :
    hsearch_bi_state V heur :=
  ⟨biExpand G heur s.1, by
    obtain ⟨st, h⟩ := s.2
    exact ⟨_, biExpand_rel G heur h _head _tail⟩⟩

def hsearch_expand_bi_root (s : hsearch_bi_state V heur) (root : StoredEntry V)
    (hq : (biPurge s.1).queue.peek = some root) : hsearch_bi_state V heur :=
  ⟨biCore G heur (biPurge s.1) root, by
    obtain ⟨st, h⟩ := s.2
    have := biExpand_rel G heur h root.1.1.1 []
    unfold biExpand at this
    rw [hq] at this
    exact ⟨_, this⟩⟩

theorem expand_bi_of_root (s : hsearch_bi_state V heur) (root : StoredEntry V)
    (hq : (biPurge s.1).queue.peek = some root) (head : V) (tail : List V) :
    hsearch_expand_bi_root G heur s root hq = hsearch_step_expand_bi G heur s head tail := by
  apply Subtype.ext
  show biCore G heur (biPurge s.1) root = biExpand G heur s.1
  unfold biExpand
  rw [hq]

/-- **The step function**: the next node is read off the queue. -/
def hsearch_bi_step :
    search_step_function (G.toWeightedDiGraph) (ℕ × ℕ) (hsearch_bi_state V heur) :=
  fun goal s =>
    match hq : (biPurge s.1).queue.peek with
    | none => (s, some false)
    | some root =>
      if root.1.1.1 = goal then (s, some true)
      else (hsearch_expand_bi_root G heur s root hq, none)

theorem hsearch_bi_step_eq :
    hsearch_bi_step G heur
      = search_stack_step (G := G.toWeightedDiGraph) (D := ℕ × ℕ)
          (state_type := hsearch_bi_state V heur) (hsearch_step_expand_bi G heur) := by
  funext goal s
  obtain ⟨st, h⟩ := s.2
  have hpk := bi_peek_eq (biPurge_rel h)
  unfold hsearch_bi_step search_stack_step
  show _ = (match (biToBase (g := G.toWeightedDiGraph) s.1).stack with
    | [] => (s, some false)
    | x :: t => if x = goal then (s, some true)
        else (hsearch_step_expand_bi G heur s x t, none))
  have hst : (st.toBaseState (g := G.toWeightedDiGraph)).stack = st.erase.queue :=
    hsearch_stored_state.storedQueue_eq st
  rw [biToBase_eq h, hst]
  split
  · next hq =>
    rw [stored_queue_nil heur st (by rw [← hpk, hq])]
  · next root hq =>
    rw [stored_queue_cons heur st root (by rw [← hpk, hq])]
    simp only
    split
    · rfl
    · rw [expand_bi_of_root G heur s root hq]

def hsearch_bi_termination_metric (s : hsearch_bi_state V heur) : ℕ × ℕ × ℕ × ℕ :=
  hsearch_termination_metric_nat (biToBase (g := G.toWeightedDiGraph) s.1)

theorem hsearch_bi_metric_eq (s : hsearch_bi_state V heur) {st : hsearch_stored_state V heur}
    (h : BIRel s.1 st) :
    hsearch_bi_termination_metric G heur s = hsearch_stored_termination_metric G heur st := by
  unfold hsearch_bi_termination_metric hsearch_stored_termination_metric
    hsearch_lazy_termination_metric
  rw [biToBase_eq h, hsearch_stored_state.toBaseState_eq]

theorem hsearch_bi_expand_metric_reduction (goal : V) :
    WeightedDiGraph.termination_proof_for_expand (G := G.toWeightedDiGraph) (D := ℕ × ℕ)
      (state_type := hsearch_bi_state V heur) (hsearch_step_expand_bi G heur) goal
      (hsearch_bi_termination_metric G heur) := by
  intro s head tail hs
  obtain ⟨st, h⟩ := s.2
  have h' := biExpand_rel G heur h head tail
  have := hsearch_stored_expand_metric_reduction G heur goal st head tail
    (by rw [← bi_to_base s h]; exact hs)
  rw [hsearch_bi_metric_eq G heur s h,
    hsearch_bi_metric_eq G heur (hsearch_step_expand_bi G heur s head tail) h']
  exact this

theorem hsearch_bi_expand_keeps_base_invars (start goal : V) :
    WeightedDiGraph.base_invar_carries_over_expand (G := G.toWeightedDiGraph) (D := ℕ × ℕ)
      (state_type := hsearch_bi_state V heur) (hsearch_step_expand_bi G heur) goal
      (WeightedDiGraph.search_invar_all_basic (G := G.toWeightedDiGraph) (D := ℕ × ℕ)
        (hsearch_expandable heur) start) := by
  intro s head tail hs
  obtain ⟨st, h⟩ := s.2
  have h' := biExpand_rel G heur h head tail
  have := hsearch_stored_expand_keeps_base_invars G heur start goal st head tail
    (by rw [← bi_to_base s h]; exact hs)
  rw [bi_to_base (hsearch_step_expand_bi G heur s head tail) h']
  exact this

theorem hsearch_bi_initial_spec (start : V) (d : ℕ × ℕ) (te : ℕ) :
    BIRel ⟨VisitedSet.singleton start, ∅, d, start,
      RQ.single bkey (((start, d), addH d (heur start)), 0), (∅ : Std.HashMap V ℕ).insert start 0,
      1, 0, te⟩ (hsearch_stored_state.initial heur start d te) := by
  refine ⟨rfl, rfl, rfl, ?_, rfl, rfl, rfl, rfl,
    (RQ.single_spec (key := bkey) (idx := bidx) (((start, d), addH d (heur start)), 0)).2, ?_⟩
  · intro v
    simp [hsearch_stored_state.initial]
  · rw [(RQ.single_spec (key := bkey) (idx := bidx) (((start, d), addH d (heur start)), 0)).1]
    simp [HeapQueue.sortedList, hsearch_stored_state.initial]

/-- The initial state: only `start` is queued. -/
def hsearch_bi_initial (start : V) (d : ℕ × ℕ) (te : ℕ) : hsearch_bi_state V heur :=
  ⟨⟨VisitedSet.singleton start, ∅, d, start,
      RQ.single bkey (((start, d), addH d (heur start)), 0), (∅ : Std.HashMap V ℕ).insert start 0,
      1, 0, te⟩, ⟨_, hsearch_bi_initial_spec heur start d te⟩⟩

theorem hsearch_bi_toBaseState_initial (start : V) (d : ℕ × ℕ) (te : ℕ) :
    has_base_search_state.to_base_state (G := G.toWeightedDiGraph) (D := ℕ × ℕ)
      (hsearch_bi_initial heur start d te) = base_search_state_initial start d := by
  rw [bi_to_base _ (hsearch_bi_initial_spec heur start d te)]
  exact hsearch_stored_toBaseState_initial G heur start d te

/-- **A\\* with stored `f`-values on a bucket queue, with one map for orders and mothers.** -/
def astar_bi_fastpath (start : V) (goal : V) (te : ℕ := 100) :
    Option ((G.toWeightedDiGraph).Path start goal) :=
  WeightedDiGraph.search_exe_with_step_eq_fast (G := G.toWeightedDiGraph) (start := start)
    (start_state := hsearch_bi_initial heur start ⟨0, 0⟩ te)
    (termination_metric := hsearch_bi_termination_metric G heur)
    (hsearch_step_expand_bi G heur) goal
    (hsearch_bi_step G heur) (hsearch_bi_step_eq G heur)
    (hsearch_bi_expand_metric_reduction G heur goal)
    (hsearch_bi_expand_keeps_base_invars G heur start goal)
    (hsearch_bi_toBaseState_initial G heur start (0, 0) te)

/-- **It returns the same path as `astar_heap_stored_fastpath`.** -/
theorem astar_bi_fastpath_eq_stored (start : V) (goal : V) (te : ℕ) :
    astar_bi_fastpath G heur start goal te = astar_heap_stored_fastpath G heur start goal te := by
  unfold astar_bi_fastpath astar_heap_stored_fastpath
  rw [WeightedDiGraph.search_exe_with_step_eq_fast_eq, WeightedDiGraph.search_exe_with_step_eq_fast_eq,
    WeightedDiGraph.search_exe_with_step_eq_stack, WeightedDiGraph.search_exe_with_step_eq_stack]
  exact search_exe_with_stack_step_sim_rel (G := G.toWeightedDiGraph) (D := ℕ × ℕ)
    (A := hsearch_bi_state V heur) (B := hsearch_stored_state V heur)
    (fun a b => BIRel a.1 b) (fun a b h => bi_to_base a h)
    (hsearch_step_expand_bi G heur) (hsearch_step_expand_stored G heur)
    (fun a b head tail h _ => biExpand_rel G heur h head tail)
    (hsearch_bi_initial_spec heur start (0, 0) te)
    (hsearch_bi_termination_metric G heur) (hsearch_stored_termination_metric G heur)
    (hsearch_bi_expand_metric_reduction G heur goal)
    (hsearch_bi_expand_keeps_base_invars G heur start goal)
    (hsearch_bi_toBaseState_initial G heur start (0, 0) te)
    (hsearch_stored_expand_metric_reduction G heur goal)
    (hsearch_stored_expand_keeps_base_invars G heur start goal)
    (hsearch_stored_toBaseState_initial G heur start (0, 0) te)

/-- Multi-goal A* on this search. -/
def astar_multigoal_bi_fastpath (start : V)
    (is_goal : V → Prop) [DecidablePred is_goal] (te : ℕ := 100) :
    Option ((thegoal : {v : V // is_goal v}) × (G.toWeightedDiGraph).Path start thegoal) :=
  astar_multigoal_postprocess (g := G.toWeightedDiGraph) start is_goal
    (astar_bi_fastpath (add_artificial_goal_gen G is_goal) (opt_heur heur) (some start) none te)

theorem astar_multigoal_bi_fastpath_eq_stored (start : V)
    (is_goal : V → Prop) [DecidablePred is_goal] (te : ℕ) :
    astar_multigoal_bi_fastpath G heur start is_goal te
      = astar_multigoal_heap_stored_fastpath G heur start is_goal te := by
  unfold astar_multigoal_bi_fastpath astar_multigoal_heap_stored_fastpath
  rw [astar_bi_fastpath_eq_stored]

end

/-- **The stored search runs on this implementation.** -/
@[csimp] theorem astar_heap_stored_fastpath_eq_bi :
    @astar_heap_stored_fastpath = @astar_bi_fastpath := by
  funext V _ _ _ _ G heur start goal te
  exact (astar_bi_fastpath_eq_stored G heur start goal te).symm

@[csimp] theorem astar_multigoal_heap_stored_fastpath_eq_bi :
    @astar_multigoal_heap_stored_fastpath = @astar_multigoal_bi_fastpath := by
  funext V _ _ _ _ G heur start is_goal _ te
  exact (astar_multigoal_bi_fastpath_eq_stored G heur start is_goal te).symm

end NatGraph
