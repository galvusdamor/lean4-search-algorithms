import Mathlib.Tactic

/-!
# A verified leftist heap

A *leftist heap* is a binary tree that is heap-ordered with respect to a comparison function
`le` and whose right spine is short (that is what the stored `rank` is for: the right spine
of a heap of `n` elements has length `O(log n)`).  All operations are implemented by a single
`merge`, which walks down the two right spines and therefore costs `O(log n)` — in the
*worst* case and, since the structure is purely functional, also when the heap is used
persistently, i.e. when several versions of it are alive at the same time.

This is what the search of `SearchAlgorithms.HeuristicSearchHeap` uses as its queue: the
elements never have to be kept in a sorted list, they are only compared on the way down the
right spine, and no array is ever copied.

The file provides the operations

* `LHeap.merge`, `LHeap.insert`, `LHeap.ofList`, `LHeap.peek`, `LHeap.deleteMin`

and their two specifications

* `LHeap.elems`, the multiset (as a list, up to `List.Perm`) of the elements stored, and
* `LHeap.Ordered`, the heap invariant "every node is `le` all elements below it".

The main results are `elems_merge`, `Ordered_merge`, `peek_le` (the root is a minimum),
`elems_deleteMin` and `Ordered_deleteMin`.
-/

namespace SearchAlgorithms

/-- A leftist heap: a binary tree whose nodes store the rank (the length of the right
spine) together with the element. -/
inductive LHeap (α : Type) where
  /-- The empty heap. -/
  | nil : LHeap α
  /-- A node with rank `rk`, element `x` and the two subheaps `l` and `r`. -/
  | node (rk : ℕ) (x : α) (l r : LHeap α) : LHeap α
deriving Inhabited

namespace LHeap

variable {α : Type}

/-- The number of elements of a heap. -/
def size : LHeap α → ℕ
  | nil => 0
  | node _ _ l r => l.size + r.size + 1

/-- The stored rank (length of the right spine); it is only used to keep the heap balanced,
never in a correctness statement. -/
def rank : LHeap α → ℕ
  | nil => 0
  | node k _ _ _ => k

/-- The elements of a heap, in an unspecified order. -/
def elems : LHeap α → List α
  | nil => []
  | node _ x l r => x :: (l.elems ++ r.elems)

@[simp] theorem elems_nil : (nil : LHeap α).elems = [] := rfl

@[simp] theorem elems_node (k : ℕ) (x : α) (l r : LHeap α) :
    (node k x l r).elems = x :: (l.elems ++ r.elems) := rfl

@[simp] theorem size_nil : (nil : LHeap α).size = 0 := rfl

@[simp] theorem size_node (k : ℕ) (x : α) (l r : LHeap α) :
    (node k x l r).size = l.size + r.size + 1 := rfl

/-- Build a node from an element and two subheaps, putting the subheap of larger rank on the
left (this is what keeps the right spine short). -/
def mkNode (x : α) (a b : LHeap α) : LHeap α :=
  if b.rank ≤ a.rank then node (b.rank + 1) x a b else node (a.rank + 1) x b a

theorem elems_mkNode (x : α) (a b : LHeap α) :
    (mkNode x a b).elems.Perm (x :: (a.elems ++ b.elems)) := by
  unfold mkNode
  split
  · exact List.Perm.refl _
  · exact List.Perm.cons x List.perm_append_comm

/-- The heap invariant: every element is `le` all the elements below it. -/
def Ordered (le : α → α → Bool) : LHeap α → Prop
  | nil => True
  | node _ x l r => (∀ y ∈ l.elems ++ r.elems, le x y = true) ∧ Ordered le l ∧ Ordered le r

@[simp] theorem Ordered_nil (le : α → α → Bool) : Ordered le (nil : LHeap α) := trivial

theorem Ordered_node_iff (le : α → α → Bool) (k : ℕ) (x : α) (l r : LHeap α) :
    Ordered le (node k x l r) ↔
      (∀ y ∈ l.elems ++ r.elems, le x y = true) ∧ Ordered le l ∧ Ordered le r := Iff.rfl

theorem Ordered_mkNode (le : α → α → Bool) (x : α) (a b : LHeap α)
    (hx : ∀ y ∈ a.elems ++ b.elems, le x y = true)
    (ha : Ordered le a) (hb : Ordered le b) : Ordered le (mkNode x a b) := by
  unfold mkNode
  split
  · exact ⟨hx, ha, hb⟩
  · refine ⟨?_, hb, ha⟩
    intro y hy
    exact hx y ((List.perm_append_comm (l₁ := b.elems) (l₂ := a.elems)).subset hy)

/-- Merge two heaps. -/
def merge (le : α → α → Bool) : LHeap α → LHeap α → LHeap α
  | nil, h => h
  | h, nil => h
  | node k₁ x l₁ r₁, node k₂ y l₂ r₂ =>
      if le x y then mkNode x l₁ (merge le r₁ (node k₂ y l₂ r₂))
      else mkNode y l₂ (merge le (node k₁ x l₁ r₁) r₂)
termination_by h₁ h₂ => h₁.size + h₂.size

@[simp] theorem merge_nil_left (le : α → α → Bool) (h : LHeap α) : merge le nil h = h := by
  rw [merge]

@[simp] theorem merge_nil_right (le : α → α → Bool) (h : LHeap α) : merge le h nil = h := by
  cases h with
  | nil => rw [merge]
  | node k x l r => rw [merge]; simp

theorem merge_node_node (le : α → α → Bool) (k₁ : ℕ) (x : α) (l₁ r₁ : LHeap α)
    (k₂ : ℕ) (y : α) (l₂ r₂ : LHeap α) :
    merge le (node k₁ x l₁ r₁) (node k₂ y l₂ r₂) =
      if le x y then mkNode x l₁ (merge le r₁ (node k₂ y l₂ r₂))
      else mkNode y l₂ (merge le (node k₁ x l₁ r₁) r₂) := by
  rw [merge]

/-- The elements of a merge are the elements of the two heaps. -/
theorem elems_merge (le : α → α → Bool) : ∀ (h₁ h₂ : LHeap α),
    (merge le h₁ h₂).elems.Perm (h₁.elems ++ h₂.elems)
  | nil, h => by simp
  | node k₁ x l₁ r₁, nil => by simp
  | node k₁ x l₁ r₁, node k₂ y l₂ r₂ => by
    rw [merge_node_node]
    split
    · refine (elems_mkNode _ _ _).trans ?_
      refine List.Perm.cons x ?_
      refine ((elems_merge le r₁ (node k₂ y l₂ r₂)).append_left l₁.elems).trans ?_
      simp only [elems_node]
      exact (List.append_assoc _ _ _ ▸ List.Perm.refl _)
    · refine (elems_mkNode _ _ _).trans ?_
      refine (List.Perm.cons y ((elems_merge le (node k₁ x l₁ r₁) r₂).append_left l₂.elems)).trans ?_
      simp only [elems_node]
      exact (List.Perm.cons y (List.perm_append_comm_assoc _ _ _)).trans List.perm_middle.symm
termination_by h₁ h₂ => h₁.size + h₂.size

theorem mem_merge (le : α → α → Bool) (h₁ h₂ : LHeap α) (a : α) :
    a ∈ (merge le h₁ h₂).elems ↔ a ∈ h₁.elems ∨ a ∈ h₂.elems := by
  rw [(elems_merge le h₁ h₂).mem_iff, List.mem_append]

/-- `merge` preserves the heap invariant. -/
theorem Ordered_merge (le : α → α → Bool)
    (total : ∀ a b, (le a b || le b a) = true)
    (trans : ∀ a b c, le a b → le b c → le a c) : ∀ (h₁ h₂ : LHeap α),
    Ordered le h₁ → Ordered le h₂ → Ordered le (merge le h₁ h₂)
  | nil, h, _, h2 => by simpa using h2
  | node k₁ x l₁ r₁, nil, h1, _ => by simpa using h1
  | node k₁ x l₁ r₁, node k₂ y l₂ r₂, h1, h2 => by
    obtain ⟨hx, hl₁, hr₁⟩ := h1
    obtain ⟨hy, hl₂, hr₂⟩ := h2
    rw [merge_node_node]
    split
    · next hxy =>
      refine Ordered_mkNode le _ _ _ ?_ hl₁
        (Ordered_merge le total trans r₁ (node k₂ y l₂ r₂) hr₁ ⟨hy, hl₂, hr₂⟩)
      intro z hz
      rcases List.mem_append.mp hz with hz | hz
      · exact hx z (List.mem_append.mpr (Or.inl hz))
      · rcases (mem_merge le r₁ (node k₂ y l₂ r₂) z).mp hz with hz | hz
        · exact hx z (List.mem_append.mpr (Or.inr hz))
        · rcases List.mem_cons.mp hz with rfl | hz
          · exact hxy
          · exact trans _ _ _ hxy (hy z hz)
    · next hxy =>
      have hyx : le y x = true := by
        have := total x y
        simp only [hxy, Bool.false_or] at this
        simpa using this
      refine Ordered_mkNode le _ _ _ ?_ hl₂
        (Ordered_merge le total trans (node k₁ x l₁ r₁) r₂ ⟨hx, hl₁, hr₁⟩ hr₂)
      intro z hz
      rcases List.mem_append.mp hz with hz | hz
      · exact hy z (List.mem_append.mpr (Or.inl hz))
      · rcases (mem_merge le (node k₁ x l₁ r₁) r₂ z).mp hz with hz | hz
        · rcases List.mem_cons.mp hz with rfl | hz
          · exact hyx
          · exact trans _ _ _ hyx (hx z hz)
        · exact hy z (List.mem_append.mpr (Or.inr hz))
termination_by h₁ h₂ => h₁.size + h₂.size

/-- Insert an element. -/
def insert (le : α → α → Bool) (h : LHeap α) (x : α) : LHeap α :=
  merge le (node 1 x nil nil) h

theorem elems_insert (le : α → α → Bool) (h : LHeap α) (x : α) :
    (insert le h x).elems.Perm (x :: h.elems) := by
  refine (elems_merge le (node 1 x nil nil) h).trans ?_
  simp

theorem Ordered_insert (le : α → α → Bool)
    (total : ∀ a b, (le a b || le b a) = true)
    (trans : ∀ a b c, le a b → le b c → le a c) (h : LHeap α) (x : α)
    (hh : Ordered le h) : Ordered le (insert le h x) :=
  Ordered_merge le total trans _ _ (by simp [Ordered]) hh

/-- Inserting all the elements of a list into a heap. -/
theorem elems_foldl_insert (le : α → α → Bool) : ∀ (l : List α) (h : LHeap α),
    (l.foldl (insert le) h).elems.Perm (h.elems ++ l)
  | [], h => by simp
  | a :: t, h => by
    refine (elems_foldl_insert le t (insert le h a)).trans ?_
    refine ((elems_insert le h a).append_right t).trans ?_
    exact (List.perm_middle).symm

theorem Ordered_foldl_insert (le : α → α → Bool)
    (total : ∀ a b, (le a b || le b a) = true)
    (trans : ∀ a b c, le a b → le b c → le a c) : ∀ (l : List α) (h : LHeap α),
    Ordered le h → Ordered le (l.foldl (insert le) h)
  | [], h, hh => by simpa using hh
  | a :: t, h, hh =>
    Ordered_foldl_insert le total trans t _ (Ordered_insert le total trans h a hh)

/-- Build a heap from a list. -/
def ofList (le : α → α → Bool) (l : List α) : LHeap α := l.foldl (insert le) nil

theorem elems_ofList (le : α → α → Bool) (l : List α) : (ofList le l).elems.Perm l := by
  unfold ofList
  simpa using elems_foldl_insert le l nil

theorem Ordered_ofList (le : α → α → Bool)
    (total : ∀ a b, (le a b || le b a) = true)
    (trans : ∀ a b c, le a b → le b c → le a c) (l : List α) :
    Ordered le (ofList le l) :=
  Ordered_foldl_insert le total trans l nil (by simp)

/-- The minimum of the heap, if any. -/
def peek : LHeap α → Option α
  | nil => none
  | node _ x _ _ => some x

/-- Remove the minimum. -/
def deleteMin (le : α → α → Bool) : LHeap α → LHeap α
  | nil => nil
  | node _ _ l r => merge le l r

@[simp] theorem peek_nil : (nil : LHeap α).peek = none := rfl

@[simp] theorem peek_node (k : ℕ) (x : α) (l r : LHeap α) : (node k x l r).peek = some x := rfl

theorem peek_eq_none_iff (h : LHeap α) : h.peek = none ↔ h.elems = [] := by
  cases h <;> simp [peek]

theorem peek_eq_some_iff (h : LHeap α) (x : α) :
    h.peek = some x ↔ ∃ t, h.elems = x :: t := by
  cases h with
  | nil => simp [peek]
  | node k y l r => simp [peek, eq_comm]

/-- **The root of an ordered heap is a minimum.** -/
theorem peek_le (le : α → α → Bool) (h : LHeap α) (hh : Ordered le h) (x : α)
    (hx : h.peek = some x) : ∀ y ∈ h.elems, le x y = true ∨ y = x := by
  cases h with
  | nil => simp at hx
  | node k z l r =>
    simp only [peek_node, Option.some.injEq] at hx
    subst hx
    intro y hy
    rcases List.mem_cons.mp hy with rfl | hy
    · exact Or.inr rfl
    · exact Or.inl (hh.1 y hy)

theorem elems_deleteMin (le : α → α → Bool) (h : LHeap α) (x : α) (hx : h.peek = some x) :
    h.elems.Perm (x :: (deleteMin le h).elems) := by
  cases h with
  | nil => simp at hx
  | node k z l r =>
    simp only [peek_node, Option.some.injEq] at hx
    subst hx
    exact List.Perm.cons _ (elems_merge le l r).symm

theorem Ordered_deleteMin (le : α → α → Bool)
    (total : ∀ a b, (le a b || le b a) = true)
    (trans : ∀ a b c, le a b → le b c → le a c) (h : LHeap α) (hh : Ordered le h) :
    Ordered le (deleteMin le h) := by
  cases h with
  | nil => simp [deleteMin]
  | node k z l r => exact Ordered_merge le total trans l r hh.2.1 hh.2.2

/-- The heap invariant only depends on the comparison of the elements actually stored. -/
theorem Ordered_congr (le le' : α → α → Bool) : ∀ (h : LHeap α),
    (∀ a ∈ h.elems, ∀ b ∈ h.elems, le a b = le' a b) → Ordered le h → Ordered le' h
  | nil, _, _ => trivial
  | node k x l r, hcong, ⟨hx, hl, hr⟩ => by
    refine ⟨?_, ?_, ?_⟩
    · intro y hy
      rw [← hcong x (by simp) y (by simp [hy]), hx y hy]
    · refine Ordered_congr le le' l ?_ hl
      intro a ha b hb
      exact hcong a (by simp [ha]) b (by simp [hb])
    · refine Ordered_congr le le' r ?_ hr
      intro a ha b hb
      exact hcong a (by simp [ha]) b (by simp [hb])

/-- **`deleteMin` with a changed comparison function.**  For the result to be a heap the two
comparison functions only have to agree on the *remaining* elements: the element that is
removed may well have changed its position in the order. -/
theorem Ordered_deleteMin_of_congr (le le' : α → α → Bool)
    (total : ∀ a b, (le' a b || le' b a) = true)
    (trans : ∀ a b c, le' a b → le' b c → le' a c)
    (h : LHeap α) (hord : Ordered le h)
    (hcong : ∀ a ∈ (deleteMin le' h).elems, ∀ b ∈ (deleteMin le' h).elems, le a b = le' a b) :
    Ordered le' (deleteMin le' h) := by
  cases h with
  | nil => simp [deleteMin]
  | node k x l r =>
    obtain ⟨-, hl, hr⟩ := hord
    have hmem : ∀ a, a ∈ l.elems ∨ a ∈ r.elems → a ∈ (deleteMin le' (node k x l r)).elems :=
      fun a ha => (mem_merge le' l r a).mpr ha
    refine Ordered_merge le' total trans l r ?_ ?_
    · refine Ordered_congr le le' l ?_ hl
      intro a ha b hb
      exact hcong a (hmem a (Or.inl ha)) b (hmem b (Or.inl hb))
    · refine Ordered_congr le le' r ?_ hr
      intro a ha b hb
      exact hcong a (hmem a (Or.inr ha)) b (hmem b (Or.inr hb))

end LHeap

end SearchAlgorithms
