import Mathlib.Tactic

/-!
# A bucket queue

The entries of a search queue are ordered by a key `key e : ℕ × ℕ` (lexicographically) and,
among equal keys, by an insertion number `idx e`.  When the entries are inserted with
increasing insertion numbers, a queue with one FIFO bucket per key pops them in exactly this
order: the buckets are kept sorted by key, and a bucket is a pair of lists (`front`, and
`back` reversed).  Popping and pushing are `O(1)` (amortised), plus a walk along the buckets
to the key of a pushed entry — which, in a search, is close to the front.

`BQ.WF` is the invariant; under it the elements of the queue (`BQ.elems`: the buckets in
order) are sorted by key and insertion number (`BQ.sorted_elems`), `peek` is their head and
`pop` removes it (`BQ.peek_eq`, `BQ.elems_pop`), and `insert` adds an entry
(`BQ.elems_insert`), preserving the invariant when its insertion number is larger than all
in the queue (`BQ.WF_insert`).
-/

namespace SearchAlgorithms

/-- The strict lexicographic order on keys. -/
@[inline] def keyLt (a b : ℕ × ℕ) : Bool := a.1 < b.1 || (a.1 == b.1 && a.2 < b.2)

theorem keyLt_iff (a b : ℕ × ℕ) : keyLt a b = true ↔ a.1 < b.1 ∨ (a.1 = b.1 ∧ a.2 < b.2) := by
  simp [keyLt]

theorem keyLt_trans {a b c : ℕ × ℕ} (h1 : keyLt a b = true) (h2 : keyLt b c = true) :
    keyLt a c = true := by
  rw [keyLt_iff] at *; omega

theorem keyLt_irrefl (a : ℕ × ℕ) : keyLt a a = false := by
  simp [keyLt]

theorem keyLt_total {a b : ℕ × ℕ} (h1 : ¬ a = b) (h2 : keyLt a b = false) : keyLt b a = true := by
  rw [keyLt_iff]
  have : ¬ (a.1 < b.1 ∨ (a.1 = b.1 ∧ a.2 < b.2)) := by rw [← keyLt_iff]; simp [h2]
  have hne : a.1 ≠ b.1 ∨ a.2 ≠ b.2 := by
    by_contra hc; push_neg at hc; exact h1 (Prod.ext hc.1 hc.2)
  omega

/-- A bucket: the entries of one key, first `front` then `back` reversed. -/
structure Bucket (α : Type) where
  key : ℕ × ℕ
  front : List α
  back : List α

/-- The entries of a bucket, in order. -/
def Bucket.elems {α : Type} (b : Bucket α) : List α := b.front ++ b.back.reverse

/-- A bucket queue: its buckets, sorted by key. -/
abbrev BQ (α : Type) := List (Bucket α)

namespace BQ

variable {α : Type}

/-- The entries of the queue, in order. -/
def elems (q : BQ α) : List α := q.flatMap Bucket.elems

/-- The first entry. -/
@[inline] def peek : BQ α → Option α
  | [] => none
  | b :: _ => b.front.head?

/-- Remove the first entry. -/
@[inline] def pop : BQ α → BQ α
  | [] => []
  | b :: r => match b.front with
    | [] => r
    | [_] => match b.back with
      | [] => r
      | y :: ys => ⟨b.key, (y :: ys).reverse, []⟩ :: r
    | _ :: x :: f => ⟨b.key, x :: f, b.back⟩ :: r

/-- Add an entry at the end of the bucket of its key. -/
@[specialize] def insert (key : α → ℕ × ℕ) : BQ α → α → BQ α
  | [], e => [⟨key e, [e], []⟩]
  | b :: r, e =>
    if key e == b.key then ⟨b.key, b.front, e :: b.back⟩ :: r
    else if keyLt (key e) b.key then ⟨key e, [e], []⟩ :: b :: r
    else b :: insert key r e

/-- Add the entries of a list, in order. -/
@[specialize] def insertAll (key : α → ℕ × ℕ) (q : BQ α) (l : List α) : BQ α :=
  l.foldl (insert key) q

/-- The invariant: buckets sorted by key, non-empty fronts, every entry in the bucket of its
key, and the entries of a bucket in increasing insertion order. -/
def WF (key : α → ℕ × ℕ) (idx : α → ℕ) (q : BQ α) : Prop :=
  q.Pairwise (fun b c => keyLt b.key c.key = true) ∧ (∀ b ∈ q, b.front ≠ []) ∧
    (∀ b ∈ q, ∀ e ∈ b.elems, key e = b.key) ∧
    (∀ b ∈ q, b.elems.Pairwise (fun x y => idx x < idx y))

@[simp] theorem elems_nil : elems ([] : BQ α) = [] := rfl

@[simp] theorem elems_cons (b : Bucket α) (q : BQ α) : elems (b :: q) = b.elems ++ elems q := by
  simp [elems]

theorem mem_elems {q : BQ α} {e : α} : e ∈ elems q ↔ ∃ b ∈ q, e ∈ b.elems := by
  simp [elems]

/-- **`peek` is the head of the entries.** -/
theorem peek_eq (q : BQ α) (hf : ∀ b ∈ q, b.front ≠ []) : q.peek = (elems q).head? := by
  cases q with
  | nil => rfl
  | cons b r =>
    have := hf b List.mem_cons_self
    cases hb : b.front with
    | nil => exact absurd hb this
    | cons x f => simp [peek, hb, Bucket.elems]

/-- **`pop` removes the head of the entries.** -/
theorem elems_pop (q : BQ α) (hf : ∀ b ∈ q, b.front ≠ []) : elems (pop q) = (elems q).tail := by
  cases q with
  | nil => rfl
  | cons b r =>
    have := hf b List.mem_cons_self
    obtain ⟨k, fr, bk⟩ := b
    simp only at this
    match fr, bk, this with
    | [x], [], _ => simp [pop, Bucket.elems]
    | [x], y :: ys, _ => simp [pop, Bucket.elems]
    | x :: z :: f, bk, _ => simp [pop, Bucket.elems]

theorem pop_sub (q : BQ α) : ∀ c ∈ pop q, ∃ b ∈ q, c.key = b.key ∧
    (∀ e ∈ c.elems, e ∈ b.elems) ∧ ∃ l, b.elems = l ++ c.elems := by
  intro c hc
  cases q with
  | nil => cases hc
  | cons b r =>
    obtain ⟨k, fr, bk⟩ := b
    match fr, bk with
    | [], bk =>
      exact ⟨c, List.mem_cons_of_mem _ hc, rfl, fun e he => he, [], rfl⟩
    | [x], [] =>
      exact ⟨c, List.mem_cons_of_mem _ hc, rfl, fun e he => he, [], rfl⟩
    | [x], y :: ys =>
      simp only [pop, List.mem_cons] at hc
      rcases hc with rfl | hc
      · refine ⟨⟨k, [x], y :: ys⟩, List.mem_cons_self, rfl, ?_, [x], ?_⟩
        · intro e he; simp [Bucket.elems] at he ⊢; tauto
        · simp [Bucket.elems]
      · exact ⟨c, List.mem_cons_of_mem _ hc, rfl, fun e he => he, [], rfl⟩
    | x :: z :: f, bk =>
      simp only [pop, List.mem_cons] at hc
      rcases hc with rfl | hc
      · refine ⟨⟨k, x :: z :: f, bk⟩, List.mem_cons_self, rfl, ?_, [x], ?_⟩
        · intro e he; simp [Bucket.elems] at he ⊢; tauto
        · simp [Bucket.elems]
      · exact ⟨c, List.mem_cons_of_mem _ hc, rfl, fun e he => he, [], rfl⟩

theorem pop_front (q : BQ α) (hf : ∀ b ∈ q, b.front ≠ []) : ∀ c ∈ pop q, c.front ≠ [] := by
  intro c hc
  cases q with
  | nil => cases hc
  | cons b r =>
    obtain ⟨k, fr, bk⟩ := b
    match fr, bk with
    | [], bk => exact hf c (List.mem_cons_of_mem _ hc)
    | [x], [] => exact hf c (List.mem_cons_of_mem _ hc)
    | [x], y :: ys =>
      simp only [pop, List.mem_cons] at hc
      rcases hc with rfl | hc
      · simp
      · exact hf c (List.mem_cons_of_mem _ hc)
    | x :: z :: f, bk =>
      simp only [pop, List.mem_cons] at hc
      rcases hc with rfl | hc
      · simp
      · exact hf c (List.mem_cons_of_mem _ hc)

theorem pop_pairwise (q : BQ α) (hp : q.Pairwise (fun b c => keyLt b.key c.key = true)) :
    (pop q).Pairwise (fun b c => keyLt b.key c.key = true) := by
  cases q with
  | nil => exact List.Pairwise.nil
  | cons b r =>
    obtain ⟨k, fr, bk⟩ := b
    rw [List.pairwise_cons] at hp
    match fr, bk with
    | [], bk => exact hp.2
    | [x], [] => exact hp.2
    | [x], y :: ys => exact List.pairwise_cons.2 ⟨fun c hc => hp.1 c hc, hp.2⟩
    | x :: z :: f, bk => exact List.pairwise_cons.2 ⟨fun c hc => hp.1 c hc, hp.2⟩

variable {key : α → ℕ × ℕ} {idx : α → ℕ}

theorem WF_pop {q : BQ α} (h : WF key idx q) : WF key idx (pop q) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨pop_pairwise q h1, pop_front q h2, ?_, ?_⟩
  · intro c hc e he
    obtain ⟨b, hb, hk, hsub, -⟩ := pop_sub q c hc
    rw [hk]; exact h3 b hb e (hsub e he)
  · intro c hc
    obtain ⟨b, hb, -, -, l, hl⟩ := pop_sub q c hc
    have := h4 b hb
    rw [hl] at this
    exact (List.pairwise_append.1 this).2.1

/-- The buckets of an insertion: the old ones (possibly with the entry added) and the new one. -/
theorem insert_buckets (r : BQ α) (e : α) : ∀ c ∈ insert key r e,
    (∃ b ∈ r, c.key = b.key ∧ (c.elems = b.elems ∨ c.elems = b.elems ++ [e])) ∨
      (c.key = key e ∧ c.elems = [e]) := by
  induction r with
  | nil => intro c hc; simp only [insert, List.mem_singleton] at hc; subst hc; right; simp [Bucket.elems]
  | cons b r ih =>
    intro c hc
    unfold insert at hc
    split at hc
    · rcases List.mem_cons.1 hc with rfl | hc
      · left; exact ⟨b, List.mem_cons_self, rfl, Or.inr (by simp [Bucket.elems])⟩
      · left; exact ⟨c, List.mem_cons_of_mem _ hc, rfl, Or.inl rfl⟩
    · split at hc
      · rcases List.mem_cons.1 hc with rfl | hc
        · right; simp [Bucket.elems]
        · left; exact ⟨c, hc, rfl, Or.inl rfl⟩
      · rcases List.mem_cons.1 hc with rfl | hc
        · left; exact ⟨c, List.mem_cons_self, rfl, Or.inl rfl⟩
        · rcases ih c hc with ⟨b', hb', h1, h2⟩ | h
          · left; exact ⟨b', List.mem_cons_of_mem _ hb', h1, h2⟩
          · right; exact h

/-- **`insert` adds the entry.** -/
theorem elems_insert (q : BQ α) (e : α) : (elems (insert key q e)).Perm (elems q ++ [e]) := by
  induction q with
  | nil => simp [insert, Bucket.elems]
  | cons b r ih =>
    unfold insert
    split
    · simp only [elems_cons, Bucket.elems, List.reverse_cons, List.append_assoc,
        List.singleton_append]
      apply List.Perm.append_left; apply List.Perm.append_left
      exact (List.perm_append_singleton _ _).symm
    · split
      · simp only [elems_cons, Bucket.elems, List.reverse_nil, List.append_nil,
          List.singleton_append, List.cons_append]
        simpa [List.append_assoc] using
          (List.perm_append_singleton e (b.front ++ (b.back.reverse ++ elems r))).symm
      · simp only [elems_cons, List.append_assoc]
        exact ih.append_left _

theorem WF_insert {q : BQ α} (h : WF key idx q) (e : α) (he : ∀ x ∈ elems q, idx x < idx e) :
    WF key idx (insert key q e) := by
  induction q with
  | nil =>
    refine ⟨List.pairwise_singleton _ _, ?_, ?_, ?_⟩ <;>
      simp [insert, Bucket.elems]
  | cons b r ih =>
    obtain ⟨h1, h2, h3, h4⟩ := h
    rw [List.pairwise_cons] at h1
    have hr : WF key idx r := ⟨h1.2, fun c hc => h2 c (List.mem_cons_of_mem _ hc),
      fun c hc => h3 c (List.mem_cons_of_mem _ hc), fun c hc => h4 c (List.mem_cons_of_mem _ hc)⟩
    have her : ∀ x ∈ elems r, idx x < idx e := fun x hx => he x (by simp [hx])
    unfold insert
    split
    · next hk =>
      have hk' : key e = b.key := by simpa using hk
      refine ⟨List.pairwise_cons.2 ⟨h1.1, h1.2⟩, ?_, ?_, ?_⟩
      · intro c hc
        rcases List.mem_cons.1 hc with rfl | hc
        · exact h2 b List.mem_cons_self
        · exact h2 c (List.mem_cons_of_mem _ hc)
      · intro c hc x hx
        rcases List.mem_cons.1 hc with rfl | hc
        · have hx' : x ∈ b.elems ∨ x = e := by
            simp only [Bucket.elems, List.reverse_cons, List.mem_append, List.mem_singleton] at hx ⊢
            tauto
          rcases hx' with hx' | rfl
          · exact h3 b List.mem_cons_self x hx'
          · exact hk'
        · exact h3 c (List.mem_cons_of_mem _ hc) x hx
      · intro c hc
        rcases List.mem_cons.1 hc with rfl | hc
        · have hb := h4 b List.mem_cons_self
          have : Bucket.elems ⟨b.key, b.front, e :: b.back⟩ = b.elems ++ [e] := by
            simp [Bucket.elems]
          rw [this, List.pairwise_append]
          refine ⟨hb, List.pairwise_singleton _ _, ?_⟩
          intro x hx y hy
          rw [List.mem_singleton] at hy; subst hy
          exact he x (by simp [hx])
        · exact h4 c (List.mem_cons_of_mem _ hc)
    · next hk =>
      have hk' : ¬ key e = b.key := by simpa using hk
      split
      · next hlt =>
        refine ⟨List.pairwise_cons.2 ⟨?_, List.pairwise_cons.2 ⟨h1.1, h1.2⟩⟩, ?_, ?_, ?_⟩
        · intro c hc
          rcases List.mem_cons.1 hc with rfl | hc
          · exact hlt
          · exact keyLt_trans hlt (h1.1 c hc)
        · intro c hc
          rcases List.mem_cons.1 hc with rfl | hc
          · simp
          · exact h2 c hc
        · intro c hc x hx
          rcases List.mem_cons.1 hc with rfl | hc
          · simp [Bucket.elems] at hx; subst hx; rfl
          · exact h3 c hc x hx
        · intro c hc
          rcases List.mem_cons.1 hc with rfl | hc
          · simp [Bucket.elems]
          · exact h4 c hc
      · next hlt =>
        have hgt : keyLt b.key (key e) = true :=
          keyLt_total hk' (by simpa using hlt)
        obtain ⟨i1, i2, i3, i4⟩ := ih hr her
        refine ⟨List.pairwise_cons.2 ⟨?_, i1⟩, ?_, ?_, ?_⟩
        · intro c hc
          rcases insert_buckets r e c hc with ⟨b', hb', hk2, -⟩ | ⟨hk2, -⟩
          · rw [hk2]; exact h1.1 b' hb'
          · rw [hk2]; exact hgt
        · intro c hc
          rcases List.mem_cons.1 hc with rfl | hc
          · exact h2 c List.mem_cons_self
          · exact i2 c hc
        · intro c hc x hx
          rcases List.mem_cons.1 hc with rfl | hc
          · exact h3 c List.mem_cons_self x hx
          · exact i3 c hc x hx
        · intro c hc
          rcases List.mem_cons.1 hc with rfl | hc
          · exact h4 c List.mem_cons_self
          · exact i4 c hc

theorem elems_insertAll (q : BQ α) (l : List α) :
    (elems (insertAll key q l)).Perm (elems q ++ l) := by
  induction l generalizing q with
  | nil => simp [insertAll]
  | cons e l ih =>
    unfold insertAll at *
    rw [List.foldl_cons]
    refine (ih _).trans ?_
    refine ((elems_insert q e).append_right l).trans ?_
    simp

theorem WF_insertAll {q : BQ α} (h : WF key idx q) (l : List α)
    (hlt : ∀ x ∈ elems q, ∀ y ∈ l, idx x < idx y) (hl : l.Pairwise (fun x y => idx x < idx y)) :
    WF key idx (insertAll key q l) := by
  induction l generalizing q with
  | nil => simpa [insertAll] using h
  | cons e l ih =>
    unfold insertAll at *
    rw [List.foldl_cons]
    rw [List.pairwise_cons] at hl
    refine ih (WF_insert h e (fun x hx => hlt x hx e List.mem_cons_self)) ?_ hl.2
    intro x hx y hy
    rcases List.mem_append.1 ((elems_insert q e).mem_iff.1 hx) with hx | hx
    · exact hlt x hx y (List.mem_cons_of_mem _ hy)
    · rw [List.mem_singleton] at hx; subst hx; exact hl.1 y hy

/-- **The entries of a well-formed queue are sorted** by key, then insertion number. -/
theorem sorted_elems {q : BQ α} (h : WF key idx q) :
    (elems q).Pairwise (fun x y => keyLt (key x) (key y) = true ∨
      (key x = key y ∧ idx x < idx y)) := by
  induction q with
  | nil => exact List.Pairwise.nil
  | cons b r ih =>
    obtain ⟨h1, h2, h3, h4⟩ := h
    rw [List.pairwise_cons] at h1
    have hr : WF key idx r := ⟨h1.2, fun c hc => h2 c (List.mem_cons_of_mem _ hc),
      fun c hc => h3 c (List.mem_cons_of_mem _ hc), fun c hc => h4 c (List.mem_cons_of_mem _ hc)⟩
    rw [elems_cons, List.pairwise_append]
    refine ⟨?_, ih hr, ?_⟩
    · refine (h4 b List.mem_cons_self).imp_of_mem ?_
      intro x y hx hy hxy
      right
      exact ⟨(h3 b List.mem_cons_self x hx).trans (h3 b List.mem_cons_self y hy).symm, hxy⟩
    · intro x hx y hy
      obtain ⟨c, hc, hyc⟩ := mem_elems.1 hy
      left
      rw [h3 b List.mem_cons_self x hx, h3 c (List.mem_cons_of_mem _ hc) y hyc]
      exact h1.1 c hc

theorem WF_nil : WF key idx ([] : BQ α) := by
  refine ⟨List.Pairwise.nil, ?_, ?_, ?_⟩ <;> simp

/-- The queue of one entry. -/
theorem WF_single (e : α) : WF key idx [⟨key e, [e], []⟩] := by
  refine ⟨List.pairwise_singleton _ _, ?_, ?_, ?_⟩ <;> simp [Bucket.elems]

/-- The size measure that `pop` decreases. -/
def size (q : BQ α) : ℕ := q.length + (elems q).length

theorem size_pop_lt (q : BQ α) (hq : q ≠ []) : size (pop q) < size q := by
  cases q with
  | nil => exact absurd rfl hq
  | cons b r =>
    obtain ⟨k, fr, bk⟩ := b
    unfold size
    match fr, bk with
    | [], bk => simp [pop]; omega
    | [x], [] => simp [pop, Bucket.elems] <;> omega
    | [x], y :: ys => simp [pop, Bucket.elems] <;> omega
    | x :: z :: f, bk => simp [pop, Bucket.elems] <;> omega

end BQ

/-! ## Buckets indexed by the first component of the key

`BQ.insert` walks along the buckets to the key of the new entry.  With many keys (action costs
make many distinct `f`-values) that walk is long, so `RQ` keeps one bucket queue per value of
the first component of the key in an array, with the index `lo` of the first non-empty one:
a push indexes the array, and only walks the (few) buckets of its `f`-value. -/

/-- Bucket queues indexed by the first component of the key. -/
structure RQ (α : Type) where
  arr : Array (BQ α)
  lo : ℕ

namespace RQ

variable {α : Type}

/-- The entries, in order. -/
def elems (r : RQ α) : List α := r.arr.toList.flatMap BQ.elems

/-- Move `lo` to the first non-empty group. -/
def norm (r : RQ α) : RQ α :=
  if h : r.lo < r.arr.size then
    if (r.arr[r.lo]).isEmpty then norm ⟨r.arr, r.lo + 1⟩ else r
  else r
termination_by r.arr.size - r.lo

/-- The first entry. -/
@[inline] def peek (r : RQ α) : Option α := (r.arr.getD r.lo []).peek

/-- Remove the first entry. -/
@[inline] def pop (r : RQ α) : RQ α := norm ⟨r.arr.modify r.lo BQ.pop, r.lo⟩

/-- Add an entry. -/
@[specialize] def insert (key : α → ℕ × ℕ) (r : RQ α) (e : α) : RQ α :=
  let i := (key e).1
  let a := if i < r.arr.size then r.arr else r.arr ++ Array.replicate (i + 1 - r.arr.size) []
  norm ⟨a.modify i (fun q => BQ.insert key q e), min r.lo i⟩

/-- Add the entries of a list, in order. -/
@[specialize] def insertAll (key : α → ℕ × ℕ) (r : RQ α) (l : List α) : RQ α :=
  l.foldl (insert key) r

variable {key : α → ℕ × ℕ} {idx : α → ℕ}

/-- The groups from index `i` on are well-formed bucket queues of the right first key. -/
def Ok (key : α → ℕ × ℕ) (idx : α → ℕ) : List (BQ α) → ℕ → Prop
  | [], _ => True
  | q :: L, i => BQ.WF key idx q ∧ (∀ e ∈ BQ.elems q, (key e).1 = i) ∧ Ok key idx L (i + 1)

/-- The invariant. -/
def WF (key : α → ℕ × ℕ) (idx : α → ℕ) (r : RQ α) : Prop :=
  Ok key idx r.arr.toList 0 ∧ (∀ j < r.lo, r.arr.toList.getD j [] = []) ∧
    (r.lo < r.arr.size → r.arr.toList.getD r.lo [] ≠ [])

theorem ok_getD : ∀ (L : List (BQ α)) (i j : ℕ), Ok key idx L i →
    BQ.WF key idx (L.getD j []) ∧ ∀ e ∈ BQ.elems (L.getD j []), (key e).1 = i + j
  | [], _, _, _ => by simp [BQ.WF_nil]
  | q :: L, i, 0, h => ⟨h.1, by simpa using h.2.1⟩
  | q :: L, i, j + 1, h => by
    have := ok_getD L (i + 1) j h.2.2
    simp only [List.getD_cons_succ]
    refine ⟨this.1, fun e he => ?_⟩
    rw [this.2 e he]; omega

theorem ok_fronts {L : List (BQ α)} {i : ℕ} (h : Ok key idx L i) (j : ℕ) :
    ∀ b ∈ L.getD j [], b.front ≠ [] := (ok_getD L i j h).1.2.1

theorem sorted_ok : ∀ (L : List (BQ α)) (i : ℕ), Ok key idx L i →
    (L.flatMap BQ.elems).Pairwise (fun x y => keyLt (key x) (key y) = true ∨
      (key x = key y ∧ idx x < idx y)) ∧ ∀ x ∈ L.flatMap BQ.elems, i ≤ (key x).1
  | [], _, _ => by simp
  | q :: L, i, h => by
    obtain ⟨h1, h2, h3⟩ := h
    obtain ⟨ih1, ih2⟩ := sorted_ok L (i + 1) h3
    rw [List.flatMap_cons, List.pairwise_append]
    refine ⟨⟨BQ.sorted_elems h1, ih1, ?_⟩, ?_⟩
    · intro x hx y hy
      left
      rw [keyLt_iff, h2 x hx]
      have := ih2 y hy
      omega
    · intro x hx
      rcases List.mem_append.1 hx with hx | hx
      · rw [h2 x hx]
      · have := ih2 x hx; omega

/-- **The entries of a well-formed queue are sorted.** -/
theorem sorted_elems {r : RQ α} (h : WF key idx r) :
    (elems r).Pairwise (fun x y => keyLt (key x) (key y) = true ∨
      (key x = key y ∧ idx x < idx y)) :=
  (sorted_ok _ 0 h.1).1

theorem peek_aux : ∀ (L : List (BQ α)) (lo i : ℕ), Ok key idx L i →
    (∀ j < lo, L.getD j [] = []) → (lo < L.length → L.getD lo [] ≠ []) →
    (L.getD lo []).peek = (L.flatMap BQ.elems).head?
  | [], lo, _, _, _, _ => by simp [BQ.peek]
  | q :: L, 0, i, h, _, hne => by
    have hq : q ≠ [] := by simpa using hne (by simp)
    simp only [List.getD_cons_zero, List.flatMap_cons]
    rw [BQ.peek_eq q h.1.2.1]
    obtain ⟨b, r, rfl⟩ : ∃ b r, q = b :: r := by
      cases q with
      | nil => exact absurd rfl hq
      | cons b r => exact ⟨b, r, rfl⟩
    have hb : b.front ≠ [] := h.1.2.1 b List.mem_cons_self
    obtain ⟨x, f, hf⟩ : ∃ x f, b.front = x :: f := by
      cases hfr : b.front with
      | nil => exact absurd hfr hb
      | cons x f => exact ⟨x, f, rfl⟩
    simp [BQ.elems, Bucket.elems, hf]
  | q :: L, lo + 1, i, h, hlo, hne => by
    have hq : q = [] := by simpa using hlo 0 (by omega)
    subst hq
    simp only [List.getD_cons_succ, List.flatMap_cons, BQ.elems_nil, List.nil_append]
    exact peek_aux L lo (i + 1) h.2.2 (fun j hj => by simpa using hlo (j + 1) (by omega))
      (fun hl => by simpa using hne (by simpa using hl))

/-- **`peek` is the head of the entries.** -/
theorem peek_eq {r : RQ α} (h : WF key idx r) : r.peek = (elems r).head? := by
  unfold peek elems
  rw [Array.getD_eq_getD_getElem?, ← Array.getElem?_toList, ← List.getD_eq_getElem?_getD]
  exact peek_aux _ r.lo 0 h.1 h.2.1 (fun hl => h.2.2 (by simpa using hl))

theorem pop_aux : ∀ (L : List (BQ α)) (lo i : ℕ), Ok key idx L i →
    (∀ j < lo, L.getD j [] = []) → (lo < L.length → L.getD lo [] ≠ []) →
    (L.modify lo BQ.pop).flatMap BQ.elems = (L.flatMap BQ.elems).tail ∧
      Ok key idx (L.modify lo BQ.pop) i
  | [], lo, _, _, _, _ => by simp [Ok]
  | q :: L, 0, i, h, _, hne => by
    have hq0 : q ≠ [] := by simpa using hne (by simp)
    simp only [List.modify_zero_cons, List.flatMap_cons]
    obtain ⟨h1, h2, h3⟩ := h
    refine ⟨?_, BQ.WF_pop h1, ?_, h3⟩
    · rw [BQ.elems_pop q h1.2.1]
      cases hq : BQ.elems q with
      | nil =>
        exfalso
        cases q with
        | nil => exact hq0 rfl
        | cons b r =>
          have hb := h1.2.1 b List.mem_cons_self
          simp [BQ.elems, Bucket.elems] at hq
          exact hb hq.1
      | cons x t => simp
    · intro e he
      rw [BQ.elems_pop q h1.2.1] at he
      exact h2 e (List.mem_of_mem_tail he)
  | q :: L, lo + 1, i, h, hlo, hne => by
    have hq : q = [] := by simpa using hlo 0 (by omega)
    subst hq
    simp only [List.modify_succ_cons, List.flatMap_cons, BQ.elems_nil, List.nil_append]
    obtain ⟨-, -, h3⟩ := h
    obtain ⟨a, b⟩ := pop_aux L lo (i + 1) h3 (fun j hj => by simpa using hlo (j + 1) (by omega))
      (fun hl => by simpa using hne (by simpa using hl))
    exact ⟨a, BQ.WF_nil, by simp, b⟩

theorem norm_arr : ∀ (r : RQ α), (norm r).arr = r.arr := by
  intro r
  induction r using norm.induct with
  | case1 r h he ih => rw [norm, dif_pos h, if_pos he]; exact ih
  | case2 r h he => rw [norm, dif_pos h, if_neg he]
  | case3 r h => rw [norm, dif_neg h]

theorem norm_spec : ∀ (r : RQ α), (∀ j < r.lo, r.arr.toList.getD j [] = []) →
    (∀ j < (norm r).lo, r.arr.toList.getD j [] = []) ∧
      ((norm r).lo < r.arr.size → r.arr.toList.getD (norm r).lo [] ≠ []) := by
  intro r
  induction r using norm.induct with
  | case1 r h he ih =>
    intro hlo
    rw [norm, dif_pos h, if_pos he]
    apply ih
    intro j hj
    rcases Nat.lt_or_ge j r.lo with hj' | hj'
    · exact hlo j hj'
    · have : j = r.lo := by simp at hj; omega
      subst this
      rw [List.getD_eq_getElem?_getD, Array.getElem?_toList, Array.getElem?_eq_getElem h]
      simpa using he
  | case2 r h he =>
    intro hlo
    rw [norm, dif_pos h, if_neg he]
    refine ⟨hlo, fun _ => ?_⟩
    rw [List.getD_eq_getElem?_getD, Array.getElem?_toList, Array.getElem?_eq_getElem h]
    simpa using he
  | case3 r h =>
    intro hlo
    rw [norm, dif_neg h]
    exact ⟨hlo, fun h' => absurd h' h⟩

theorem WF_norm {a : Array (BQ α)} {lo : ℕ} (hok : Ok key idx a.toList 0)
    (hlo : ∀ j < lo, a.toList.getD j [] = []) : WF key idx (norm ⟨a, lo⟩) := by
  have h1 := norm_arr ⟨a, lo⟩
  obtain ⟨h2, h3⟩ := norm_spec ⟨a, lo⟩ hlo
  refine ⟨?_, ?_, ?_⟩
  · rw [h1]; exact hok
  · rw [h1]; exact h2
  · rw [h1]; exact h3

/-- **`pop` removes the head of the entries.** -/
theorem elems_pop {r : RQ α} (h : WF key idx r) : elems (pop r) = (elems r).tail := by
  unfold pop elems
  rw [norm_arr, Array.toList_modify]
  exact (pop_aux _ r.lo 0 h.1 h.2.1 (fun hl => h.2.2 (by simpa using hl))).1

theorem WF_pop {r : RQ α} (h : WF key idx r) : WF key idx (pop r) := by
  unfold pop
  refine WF_norm ?_ ?_
  · rw [Array.toList_modify]
    exact (pop_aux _ r.lo 0 h.1 h.2.1 (fun hl => h.2.2 (by simpa using hl))).2
  · intro j hj
    have := h.2.1 j hj
    simp only [List.getD_eq_getElem?_getD] at this
    simpa [Array.toList_modify, List.getD_eq_getElem?_getD, List.getElem?_modify,
      show r.lo ≠ j by omega] using this

theorem insert_aux (e : α) : ∀ (L : List (BQ α)) (j i : ℕ), Ok key idx L i →
    (key e).1 = i + j → j < L.length →
    (∀ x ∈ L.flatMap BQ.elems, idx x < idx e) →
    ((L.modify j (fun q => BQ.insert key q e)).flatMap BQ.elems).Perm
        (L.flatMap BQ.elems ++ [e]) ∧
      Ok key idx (L.modify j (fun q => BQ.insert key q e)) i
  | [], _, _, _, _, hj, _ => by simp at hj
  | q :: L, 0, i, h, hk, _, hlt => by
    obtain ⟨h1, h2, h3⟩ := h
    simp only [List.modify_zero_cons, List.flatMap_cons]
    refine ⟨?_, BQ.WF_insert h1 e (fun x hx => hlt x (by simp [hx])), ?_, h3⟩
    · refine ((BQ.elems_insert q e).append_right _).trans ?_
      simp only [List.append_assoc]
      exact List.Perm.append_left _ List.perm_append_comm
    · intro x hx
      rcases List.mem_append.1 ((BQ.elems_insert q e).mem_iff.1 hx) with hx | hx
      · exact h2 x hx
      · rw [List.mem_singleton] at hx; subst hx; omega
  | q :: L, j + 1, i, h, hk, hj, hlt => by
    obtain ⟨h1, h2, h3⟩ := h
    simp only [List.modify_succ_cons, List.flatMap_cons]
    obtain ⟨a, b⟩ := insert_aux e L j (i + 1) h3 (by omega) (by simpa using hj)
      (fun x hx => hlt x (by simp [hx]))
    refine ⟨?_, h1, h2, b⟩
    simp only [List.append_assoc]
    exact a.append_left _

theorem ok_append_empty : ∀ (L : List (BQ α)) (i k : ℕ), Ok key idx L i →
    Ok key idx (L ++ List.replicate k []) i
  | [], i, 0, _ => trivial
  | [], i, k + 1, _ => by
    simp only [List.nil_append, List.replicate_succ]
    exact ⟨BQ.WF_nil, by simp, ok_append_empty [] (i + 1) k trivial⟩
  | q :: L, i, k, h => ⟨h.1, h.2.1, ok_append_empty L (i + 1) k h.2.2⟩

theorem getD_append_replicate_nil : ∀ (L : List (BQ α)) (k j : ℕ),
    (L ++ List.replicate k []).getD j [] = L.getD j []
  | [], k, j => by
    induction k generalizing j with
    | zero => rfl
    | succ k ih => cases j with
      | zero => simp [List.replicate_succ]
      | succ j => simp only [List.nil_append, List.replicate_succ, List.getD_cons_succ]; simpa using ih j
  | q :: L, k, 0 => rfl
  | q :: L, k, j + 1 => by simp only [List.cons_append, List.getD_cons_succ]; exact getD_append_replicate_nil L k j

/-- **`insert` adds the entry.** -/
theorem elems_insert_WF {r : RQ α} (h : WF key idx r) (e : α)
    (hlt : ∀ x ∈ elems r, idx x < idx e) :
    (elems (insert key r e)).Perm (elems r ++ [e]) ∧ WF key idx (insert key r e) := by
  unfold insert
  simp only
  set i := (key e).1 with hi
  set a := (if i < r.arr.size then r.arr else r.arr ++ Array.replicate (i + 1 - r.arr.size) [])
    with ha
  have hsize : i < a.size := by
    rw [ha]; split
    · assumption
    · simp; omega
  have hal : a.toList.flatMap BQ.elems = r.arr.toList.flatMap BQ.elems := by
    rw [ha]; split
    · rfl
    · simp [List.flatMap_append]
  have hok : Ok key idx a.toList 0 := by
    rw [ha]; split
    · exact h.1
    · rw [Array.toList_append, Array.toList_replicate]; exact ok_append_empty _ 0 _ h.1
  have hget : ∀ j, a.toList.getD j [] = r.arr.toList.getD j [] := by
    intro j
    rw [ha]; split
    · rfl
    · rw [Array.toList_append, Array.toList_replicate, getD_append_replicate_nil]
  obtain ⟨hp, hok'⟩ := insert_aux e a.toList i 0 hok (by omega) (by simpa using hsize)
    (by rw [hal]; exact hlt)
  refine ⟨?_, ?_⟩
  · unfold elems
    rw [norm_arr, Array.toList_modify]
    refine hp.trans ?_
    rw [hal]
  · refine WF_norm ?_ ?_
    · rw [Array.toList_modify]; exact hok'
    · intro j hj
      have := hget j
      have h2 := h.2.1 j (by omega)
      rw [h2] at this
      simp only [List.getD_eq_getElem?_getD] at this
      simpa [Array.toList_modify, List.getD_eq_getElem?_getD, List.getElem?_modify,
        show i ≠ j by omega] using this

theorem elems_insertAll_WF : ∀ (l : List α) (r : RQ α), WF key idx r →
    (∀ x ∈ elems r, ∀ y ∈ l, idx x < idx y) → l.Pairwise (fun x y => idx x < idx y) →
    (elems (insertAll key r l)).Perm (elems r ++ l) ∧ WF key idx (insertAll key r l)
  | [], r, h, _, _ => by simpa [insertAll] using h
  | e :: l, r, h, hlt, hl => by
    unfold insertAll
    rw [List.foldl_cons]
    rw [List.pairwise_cons] at hl
    obtain ⟨p1, w1⟩ := elems_insert_WF h e (fun x hx => hlt x hx e List.mem_cons_self)
    obtain ⟨p2, w2⟩ := elems_insertAll_WF l (insert key r e) w1 (by
      intro x hx y hy
      rcases List.mem_append.1 (p1.mem_iff.1 hx) with hx | hx
      · exact hlt x hx y (List.mem_cons_of_mem _ hy)
      · rw [List.mem_singleton] at hx; subst hx; exact hl.1 y hy) hl.2
    refine ⟨?_, w2⟩
    refine p2.trans ?_
    refine (p1.append_right l).trans ?_
    simp

/-- The queue of one entry. -/
def single (key : α → ℕ × ℕ) (e : α) : RQ α := insert key ⟨#[], 0⟩ e

theorem single_spec (e : α) : elems (single key e) = [e] ∧ WF key idx (single key e) := by
  have h0 : WF key idx (⟨#[], 0⟩ : RQ α) := ⟨trivial, by simp, by simp⟩
  obtain ⟨p, w⟩ := elems_insert_WF h0 e (by simp [elems])
  refine ⟨?_, w⟩
  simp only [elems, Array.toList_empty, List.flatMap_nil, List.nil_append] at p
  exact p.eq_singleton

/-- A measure that `pop` decreases on a non-empty queue. -/
def size (r : RQ α) : ℕ := (elems r).length

end RQ

namespace RQ

variable {α : Type}

/-- The measure that `pop` decreases on a queue with a first entry. -/
def msize (r : RQ α) : ℕ := (r.arr.toList.map BQ.size).sum

theorem msize_aux : ∀ (L : List (BQ α)) (lo : ℕ), L.getD lo [] ≠ [] →
    ((L.modify lo BQ.pop).map BQ.size).sum < (L.map BQ.size).sum
  | [], lo, h => by simp at h
  | q :: L, 0, h => by
    simp only [List.modify_zero_cons, List.map_cons, List.sum_cons]
    have := BQ.size_pop_lt q (by simpa using h)
    omega
  | q :: L, lo + 1, h => by
    simp only [List.modify_succ_cons, List.map_cons, List.sum_cons]
    have := msize_aux L lo (by simpa using h)
    omega

theorem norm_msize (r : RQ α) : msize (norm r) = msize r := by
  unfold msize; rw [norm_arr]

theorem msize_pop_lt (r : RQ α) (x : α) (h : r.peek = some x) : msize (pop r) < msize r := by
  unfold pop
  rw [norm_msize]
  unfold msize
  simp only [Array.toList_modify]
  apply msize_aux
  intro he
  unfold peek at h
  rw [Array.getD_eq_getD_getElem?, ← Array.getElem?_toList, ← List.getD_eq_getElem?_getD, he] at h
  cases h

end RQ

end SearchAlgorithms
