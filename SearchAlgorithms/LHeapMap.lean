import SearchAlgorithms.StaleQueue

/-!
# Mapping a leftist heap

`LHeap.map f` applies `f` to every element of a heap and keeps its shape.  The heap
operations commute with it as long as the two comparison functions *agree on the stored
elements*: `le' x y = le (f x) (f y)` for all elements `x`, `y` involved.  Nothing has to be
assumed about `f` beyond that — in particular it need not be injective.

This is what allows a search to keep extra data in its queue entries (for instance the
`f`-value of an entry, so that a comparison does not have to evaluate the heuristic) and still
be shown to perform *literally* the same heap operations as a search whose entries do not
carry it: forgetting the extra data maps the one heap onto the other
(`SearchAlgorithms.HeapLazyStored`).
-/

namespace SearchAlgorithms

namespace LHeap

variable {α β : Type}

/-- Apply `f` to every element, keeping the shape (and the ranks) of the heap. -/
def map (f : α → β) : LHeap α → LHeap β
  | nil => nil
  | node k x l r => node k (f x) (map f l) (map f r)

@[simp] theorem map_nil (f : α → β) : map f nil = nil := rfl

@[simp] theorem map_node (f : α → β) (k : ℕ) (x : α) (l r : LHeap α) :
    map f (node k x l r) = node k (f x) (map f l) (map f r) := rfl

@[simp] theorem elems_map (f : α → β) : ∀ h : LHeap α, (map f h).elems = h.elems.map f
  | nil => rfl
  | node k x l r => by simp [elems_map f l, elems_map f r]

@[simp] theorem rank_map (f : α → β) : ∀ h : LHeap α, (map f h).rank = h.rank
  | nil => rfl
  | node _ _ _ _ => rfl

@[simp] theorem size_map (f : α → β) : ∀ h : LHeap α, (map f h).size = h.size
  | nil => rfl
  | node k x l r => by simp [size_map f l, size_map f r]

@[simp] theorem peek_map (f : α → β) : ∀ h : LHeap α, (map f h).peek = h.peek.map f
  | nil => rfl
  | node _ _ _ _ => rfl

theorem map_mkNode (f : α → β) (x : α) (a b : LHeap α) :
    map f (mkNode x a b) = mkNode (f x) (map f a) (map f b) := by
  unfold mkNode
  simp only [rank_map]
  split <;> rfl

/-- The two comparison functions agree on the elements of `l`, through `f`. -/
def Agree (le' : α → α → Bool) (le : β → β → Bool) (f : α → β) (l : List α) : Prop :=
  ∀ x ∈ l, ∀ y ∈ l, le' x y = le (f x) (f y)

theorem Agree.mono {le' : α → α → Bool} {le : β → β → Bool} {f : α → β} {l l' : List α}
    (h : Agree le' le f l) (hsub : ∀ x ∈ l', x ∈ l) : Agree le' le f l' :=
  fun x hx y hy => h x (hsub x hx) y (hsub y hy)

/-- **Merging commutes with `map`** when the comparison functions agree on the elements. -/
theorem map_merge (le' : α → α → Bool) (le : β → β → Bool) (f : α → β) :
    ∀ (h₁ h₂ : LHeap α), Agree le' le f (h₁.elems ++ h₂.elems) →
      map f (merge le' h₁ h₂) = merge le (map f h₁) (map f h₂)
  | nil, h, _ => by simp
  | node k x l r, nil, _ => by simp
  | node k₁ x l₁ r₁, node k₂ y l₂ r₂, hag => by
    rw [merge_node_node, map_node, map_node, merge_node_node,
      ← hag x (by simp) y (by simp)]
    split
    · rw [map_mkNode, map_merge le' le f r₁ (node k₂ y l₂ r₂) (hag.mono (by
        intro z hz
        simp only [List.mem_append, elems_node, List.mem_cons] at hz ⊢
        tauto))]
      rfl
    · rw [map_mkNode, map_merge le' le f (node k₁ x l₁ r₁) r₂ (hag.mono (by
        intro z hz
        simp only [List.mem_append, elems_node, List.mem_cons] at hz ⊢
        tauto))]
      rfl
termination_by h₁ h₂ => h₁.size + h₂.size

theorem map_insert (le' : α → α → Bool) (le : β → β → Bool) (f : α → β) (h : LHeap α)
    (x : α) (hag : Agree le' le f (x :: h.elems)) :
    map f (insert le' h x) = insert le (map f h) (f x) := by
  unfold insert
  rw [map_merge le' le f _ _ (by simpa using hag)]
  rfl

theorem map_foldl_insert (le' : α → α → Bool) (le : β → β → Bool) (f : α → β) :
    ∀ (l : List α) (h : LHeap α), Agree le' le f (h.elems ++ l) →
      map f (l.foldl (insert le') h) = (l.map f).foldl (insert le) (map f h)
  | [], h, _ => by simp
  | a :: t, h, hag => by
    simp only [List.foldl_cons, List.map_cons]
    rw [map_foldl_insert le' le f t (insert le' h a) (hag.mono (by
        intro z hz
        rcases List.mem_append.mp hz with hz | hz
        · rcases List.mem_cons.mp ((elems_insert le' h a).mem_iff.mp hz) with rfl | hz
          · simp
          · simp [hz]
        · simp [hz])),
      map_insert le' le f h a (hag.mono (by
        intro z hz
        rcases List.mem_cons.mp hz with rfl | hz
        · simp
        · simp [hz]))]

theorem map_deleteMin (le' : α → α → Bool) (le : β → β → Bool) (f : α → β) (h : LHeap α)
    (hag : Agree le' le f h.elems) : map f (deleteMin le' h) = deleteMin le (map f h) := by
  cases h with
  | nil => rfl
  | node k x l r =>
    simp only [deleteMin, map_node]
    exact map_merge le' le f l r (hag.mono (by intro z hz; simp [hz]))

theorem Ordered_of_map (le' : α → α → Bool) (le : β → β → Bool) (f : α → β) :
    ∀ (h : LHeap α), Agree le' le f h.elems → Ordered le (map f h) → Ordered le' h
  | nil, _, _ => trivial
  | node k x l r, hag, ⟨hx, hl, hr⟩ => by
    refine ⟨?_, Ordered_of_map le' le f l (hag.mono (by intro z hz; simp [hz])) hl,
      Ordered_of_map le' le f r (hag.mono (by intro z hz; simp [hz])) hr⟩
    intro y hy
    rw [hag x (by simp) y (by simp [hy])]
    exact hx (f y) (by simpa [elems_map] using List.mem_map_of_mem hy)

end LHeap

namespace HeapQueue

variable {α β : Type}

/-- The entry map induced by a key map: the insertion number is kept. -/
def entryMap (f : α → β) (e : α × ℕ) : β × ℕ := (f e.1, e.2)

/-- **Purging commutes with mapping the keys**, when the entry orders agree on the stored
entries and liveness is read off the mapped entry. -/
theorem map_purge (le' : α → α → Bool) (le : β → β → Bool) (f : α → β) (p : β × ℕ → Bool)
    (h : LHeap (α × ℕ))
    (hag : LHeap.Agree (List.zipIdxLE le') (List.zipIdxLE le) (entryMap f) h.elems) :
    LHeap.map (entryMap f) (purge le' (p ∘ entryMap f) h)
      = purge le p (LHeap.map (entryMap f) h) := by
  rw [purge.eq_def (p := p ∘ entryMap f), purge.eq_def (p := p)]
  cases h with
  | nil => rfl
  | node k x l r =>
    simp only [LHeap.map_node, LHeap.peek_node, Function.comp_apply]
    by_cases hp : p (entryMap f x) = true
    · simp only [hp, if_true, LHeap.map_node]
    · simp only [hp, if_false, Bool.false_eq_true]
      rw [← LHeap.map_node, ← LHeap.map_deleteMin _ _ _ _ hag]
      refine map_purge le' le f p _ (hag.mono ?_)
      intro z hz
      exact (LHeap.elems_deleteMin (List.zipIdxLE le') (LHeap.node k x l r) x rfl).mem_iff.mpr
        (List.mem_cons_of_mem _ hz)
termination_by h.size
decreasing_by
  all_goals (subst_vars; simp [LHeap.deleteMin, LHeap.size_merge])

end HeapQueue

end SearchAlgorithms
