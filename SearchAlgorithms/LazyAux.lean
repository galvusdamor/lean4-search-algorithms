import Mathlib.Tactic
import Std.Data.HashMap

/-!
# Small list and hash-map lemmas used by the lazily deleted heap

These are the book-keeping facts needed in `SearchAlgorithms.HeuristicSearchHeapLazy`, where
one expansion of the search *replaces* some entries of the queue (the decrease-keys) and
appends others:

* `List.perm_map_replace` — mapping a list with a function that only moves the elements
  satisfying `c` gives a permutation of "the untouched elements, then the moved ones";
* `List.map_pair_eq_zipIdx` — a list of pairs whose second components are consecutive is a
  `zipIdx`;
* `Std.HashMap.getElem?_foldl_insert_of_mem` / `_of_not_mem` / `contains_foldl_insert` — the
  result of inserting a whole list of key/value pairs into a hash map.
-/

namespace List

variable {α β : Type}

/-- Replacing the elements satisfying `c` by `f` gives a permutation of the untouched
elements followed by the replacements. -/
theorem perm_map_replace (l : List α) (c : α → Bool) (f : α → α)
    (hf : ∀ a ∈ l, c a = false → f a = a) :
    (l.map f).Perm ((l.filter (fun a => !c a)) ++ (l.filter c).map f) := by
  induction l with
  | nil => simp
  | cons a t ih =>
    have ih' := ih (fun b hb => hf b (List.mem_cons_of_mem a hb))
    by_cases hc : c a
    · simp only [List.map_cons, List.filter_cons, hc, if_true, Bool.not_true, List.map_cons]
      simp only [Bool.false_eq_true, if_false]
      exact (ih'.cons (f a)).trans (List.perm_middle.symm)
    · have hca : c a = false := by simpa using hc
      simp only [List.map_cons, List.filter_cons, hca, Bool.not_false, if_true,
        Bool.false_eq_true, if_false, List.cons_append]
      rw [hf a (List.mem_cons_self ..) hca]
      exact ih'.cons a

/-- A list of pairs whose second components run consecutively from `k` is a `zipIdx`. -/
theorem map_pair_eq_zipIdx (l : List α) (F : α → β) (sq : α → ℕ) (k : ℕ)
    (h : ∀ (i : ℕ) (hi : i < l.length), sq l[i] = k + i) :
    l.map (fun a => (F a, sq a)) = (l.map F).zipIdx k := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    have hi : i < l.length := by simpa using h1
    simp only [List.getElem_map, List.getElem_zipIdx, h i hi]


/-- Rotating the four blocks of a double append. -/
theorem perm_append_rotate (a b c d : List α) :
    ((a ++ b) ++ (c ++ d)).Perm (((a ++ c) ++ d) ++ b) := by
  have h1 : (a ++ b) ++ (c ++ d) = a ++ (b ++ (c ++ d)) := by simp [List.append_assoc]
  have h3 : a ++ ((c ++ d) ++ b) = ((a ++ c) ++ d) ++ b := by simp [List.append_assoc]
  rw [h1, ← h3]
  exact List.Perm.append_left a List.perm_append_comm

end List

namespace Std.HashMap

variable {V A : Type} [BEq V] [LawfulBEq V] [Hashable V]

/-- Inserting a list of key/value pairs does not change the value of a key that does not
occur in the list. -/
theorem getElem?_foldl_insert_of_not_mem (key : A → V) (val : A → ℕ) (l : List A)
    (m : Std.HashMap V ℕ) (v : V) (hv : v ∉ l.map key) :
    ((l.foldl (fun m x => m.insert (key x) (val x)) m))[v]? = m[v]? := by
  induction l generalizing m with
  | nil => simp
  | cons b t ih =>
    simp only [List.map_cons, List.mem_cons, not_or] at hv
    simp only [List.foldl_cons]
    have hne : ¬ ((key b == v) = true) := by
      simp only [beq_iff_eq]
      exact fun h => hv.1 h.symm
    rw [ih _ hv.2, Std.HashMap.getElem?_insert, if_neg hne]

/-- Inserting a list of key/value pairs: the value of a key that occurs in the list (and
occurs only once) is its value in the list. -/
theorem getElem?_foldl_insert_of_mem (key : A → V) (val : A → ℕ) (l : List A)
    (hnd : (l.map key).Nodup) (m : Std.HashMap V ℕ) (a : A) (ha : a ∈ l) :
    ((l.foldl (fun m x => m.insert (key x) (val x)) m))[key a]? = some (val a) := by
  induction l generalizing m with
  | nil => simp at ha
  | cons b t ih =>
    simp only [List.map_cons, List.nodup_cons] at hnd
    rcases List.mem_cons.mp ha with rfl | hat
    · have hnot : key a ∉ t.map key := hnd.1
      simp only [List.foldl_cons]
      rw [getElem?_foldl_insert_of_not_mem key val t _ (key a) hnot,
        Std.HashMap.getElem?_insert]
      simp
    · exact ih hnd.2 _ hat

/-- Which keys a fold of insertions contains. -/
theorem contains_foldl_insert (key : A → V) (val : A → ℕ) (l : List A)
    (m : Std.HashMap V ℕ) (v : V) :
    ((l.foldl (fun m x => m.insert (key x) (val x)) m)).contains v = true
      ↔ (v ∈ l.map key ∨ m.contains v = true) := by
  induction l generalizing m with
  | nil => simp
  | cons b t ih =>
    simp only [List.foldl_cons, ih, List.map_cons, List.mem_cons, Std.HashMap.contains_insert,
      Bool.or_eq_true, beq_iff_eq]
    tauto

end Std.HashMap

namespace List

variable {α β γ : Type}

/-- The keys of a `filterMap` are a sublist of the keys of the list, provided every produced
element has the key of the element it comes from. -/
theorem map_filterMap_sublist_map (l : List α) (g : α → Option β) (key : β → γ) (f : α → γ)
    (h : ∀ a ∈ l, ∀ b, g a = some b → key b = f a) :
    ((l.filterMap g).map key).Sublist (l.map f) := by
  induction l with
  | nil => simp
  | cons a t ih =>
    have ih' := ih (fun x hx => h x (List.mem_cons_of_mem a hx))
    rw [List.filterMap_cons, List.map_cons]
    cases hg : g a with
    | none => exact ih'.trans (List.sublist_cons_self _ _)
    | some b =>
      rw [List.map_cons, h a (List.mem_cons_self ..) b hg]
      exact ih'.cons_cons _

end List
