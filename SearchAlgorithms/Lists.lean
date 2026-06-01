import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Combinatorics.Digraph.Basic
import Mathlib.Data.Bool.AllAny
import Mathlib.Data.FinEnum
import Graphlib.WF

-- theorems for `List.Pairwise`. Needed for extension of Paths with new edges, due to need to modify Nodup proofs.
theorem pairwise_add_anywhere {α: Type} {pr: α → α → Prop} {l1 l2 : List α} {symm: Symmetric pr} {a : α}:
    (∀ (a' : α), a' ∈ l1 ∨ a' ∈ l2 → pr a a') ∧ (List.Pairwise pr (l1 ++ l2))
    → (List.Pairwise pr (l1 ++ (a :: l2)))   := by
    intro ⟨ allhold, rest_of_list ⟩
    induction l1
    case nil =>
      simp
      simp at rest_of_list
      constructor
      case left =>
        intro a' inl2
        apply allhold
        right
        exact inl2
      case right => exact rest_of_list
    case cons l ls IH =>
      simp
      constructor
      case left =>
        intro a' cond
        by_cases isa : a' = a
        case pos =>
          apply symm
          simp [isa]
          apply allhold
          left
          simp
        case neg =>
          simp at rest_of_list
          have ⟨ all_condition, rest_list⟩ := rest_of_list
          apply all_condition
          cases cond
          case a.inl apinls =>
            left
            exact apinls
          case a.inr some_or =>
          cases some_or
          case inl apisa =>
            contradiction
          case inr apinl2 =>
            right
            exact apinl2
      case right =>
        apply IH
        · intro a' stuff
          apply allhold
          cases stuff
          case inl ainls =>
            left
            simp
            right
            exact ainls
          case inr ainl2=>
            right
            exact ainl2
        · simp at rest_of_list
          have ⟨ all, rest⟩ := rest_of_list
          exact rest


theorem pairwise_additional_does_not_matter {α: Type} {pr: α → α → Prop} {l1 l2 : List α} {a : α}:
    (List.Pairwise pr (l1 ++ (a :: l2))) → (List.Pairwise pr (l1 ++ l2)) := by
    induction l1
    case nil =>
      simp
    case cons l l1s IH =>
      intro longList
      simp
      constructor
      case left =>
        intro b condition
        simp at longList
        cases condition
        case inl binl1s =>
          have foo := longList.left
          apply foo
          left
          exact binl1s
        case inr binl2 =>
          have foo := longList.left
          apply foo
          right
          right
          exact binl2
      case right =>
        apply IH
        simp at longList
        exact longList.right

theorem pairwise_elem_after {α: Type} {pr: α → α → Prop} {l1 l2 : List α} {x a : α}:
    (List.Pairwise pr (l1 ++ (a :: l2))) ∧ (x ∈ l2) → pr a x := by
    intro ⟨ full_list_pairwise, xinl2 ⟩
    induction l1
    case nil => simp_all
    case cons l lss IH =>
      simp at full_list_pairwise
      apply IH
      exact full_list_pairwise.right

theorem pairwise_elem_before {α: Type} {pr: α → α → Prop} {l1 l2 : List α} {x a : α}:
    (List.Pairwise pr (l1 ++ (a :: l2))) ∧ (x ∈ l1) → pr x a := by
    intro ⟨ full_list_pairwise, xinl1 ⟩
    induction l1
    case nil => simp_all
    case cons l lss IH =>
      simp at full_list_pairwise
      have ⟨ all, rest_of_list ⟩ := full_list_pairwise
      simp at xinl1
      cases xinl1
      case inl xisl =>
        rw [xisl]
        apply all
        right
        left
        rfl
      case inr xinRest =>
        apply IH
        · exact rest_of_list
        · exact xinRest


lemma listFind_general
  (α : Type)
  (list : List α)
  (p : α → Bool)
  (hasElem : (list.findFinIdx? p).isSome) :
    p list[(list.findFinIdx? p).get hasElem] := by
  rcases Option.isSome_iff_exists.1 hasElem with ⟨i, def_some_i⟩
  simp_rw [def_some_i] -- MG: normal "simp" did not work here, but this does!
  rw [List.findFinIdx?_eq_some_iff] at def_some_i
  simp_all



def maximum_of_non_empty_list {α : Type u_1} [Max α]
  (l : List α) (non_empty : l ≠ []) : α :=
    let maxOption := l.max?
    maxOption.get (by
      unfold maxOption
      rw [Option.isSome_iff_ne_none]
      simp_all)

theorem maximum_of_non_empty_le (l : List Nat) (non_empty : l ≠ []) :
    ∀ x ∈ l, x ≤ maximum_of_non_empty_list l non_empty := by
    intro x x_in_l
    unfold maximum_of_non_empty_list
    simp_all
    apply List.le_max?_get_of_mem
    use x_in_l

theorem Option.eq_some_if_get_eq {α : Type u_1} {o : Option α} {a : α} :
      ∀ (h : o.isSome = true), o.get h = a → o = some a := by
        intro h get_is_a
        apply Option.eq_some_iff_get_eq.mpr
        use h

theorem option_mem {α : Type u_1} (o : Option α) (o_is_some : o.isSome = true) (s : Set α):
  o.get o_is_some ∈ s → ∃ x : α, o.get o_is_some = x ∧ x ∈ s := by
    intro get_in_s
    use o.get o_is_some

theorem List.get_find?_prop {α : Type u_1} {xs : List α} {p : α → Bool} (h : (find? p xs).isSome = true) : p ((find? p xs).get h) := by
  cases xs
  case nil => grind
  case cons x xs  =>
    unfold find?
    by_cases this_is_p : p x
    · simp_all
    · simp_all
      apply List.get_find?_prop

lemma List.takeWhile_until_find?_helper {α : Type u_1} [DecidableEq α] {xs : List α} {p : α → Bool}
  (h : (find? p xs).isSome = true):
    ∀ a ∈ takeWhile (fun x => !decide (x = (find? p xs).get h)) xs, p a = false := by
    cases xs
    case nil => grind
    case cons x xs =>
      unfold find?
      by_cases this_is_p : p x
      · simp_all
      · unfold takeWhile
        simp_all
        split
        · simp_all
          intro a
          apply List.takeWhile_until_find?_helper
        · simp_all

theorem List.takeWhile_until_find? {α : Type u_1} [DecidableEq α] {xs : List α} {p : α → Bool}  :
  ∀ h : (find? p xs).isSome = true,
  (List.takeWhile (fun x => decide (x ≠ (List.find? p xs).get h)) xs).all (fun x => ¬ (p x)) := by
    intro h
    grind [List.takeWhile_until_find?_helper]

theorem List.find?_nodup {α : Type u_1} {l xs : List α} {last : α} {compose : l = xs ++ [last]} {last_not_mem_xs : last ∉ xs} {p : α → Bool} { u : α } { u_mem_list : u ∈ l} {u_ne_l : u ≠ last} {u_is_p : p u} {h : (List.find? p l).isSome} :
  (List.find? p l).get h ≠ last := by
  cases l
  case nil =>
    simp_all
  case cons x xss =>
    unfold find?
    by_cases this_is_p : p x
    · simp_all
      by_contra x_is_last
      subst x_is_last
      apply List.cons_eq_append_iff.mp at compose
      cases compose
      · grind
      · next h' =>
        obtain ⟨ as', xs_head_s, _ ⟩ := h'
        simp_all
    · simp_all
      cases xs
      case neg.nil => grind
      case neg.cons y xys =>
        have x_ne_u : x ≠ u := by grind
        simp at compose
        obtain ⟨x_eq_y, compose⟩ := compose
        subst x_eq_y
        apply List.find?_nodup
        · exact compose
        · grind
        · change u ∈ xss
          grind
        · apply u_ne_l
        · exact u_is_p

theorem a_a_imp_b_to_a_and_b {a b : Prop} : (a ∧ (a → b)) → (a ∧ b) := by
  intro ⟨ a, a_to_b⟩
  and_intros
  · exact a
  · exact a_to_b a

theorem List.exists_ne_from_ne {α : Type} (n : ℕ) (l1 l2 : List α)(len1 : l1.length = n) (len2 : l2.length = n):
    l1 ≠ l2 → ∃ i : Fin n, l1[i] ≠ l2[i] ∧ ∀ j : Fin i, l1[j] = l2[j] := by
  intro not_eq
  cases l1 <;> cases l2 <;> try grind
  rename_i h1 t1 h2 t2
  by_cases h_eq : h1 = h2
  · subst h_eq
    simp [List.length_cons] at len1 len2
    have h := List.exists_ne_from_ne (n-1) t1 t2 (by omega) (by omega) (by grind)
    obtain ⟨ i, ⟨ l_prop, r_prop ⟩ ⟩ := h
    use ⟨i+1, by grind⟩
    simp_all
    intro j
    by_cases j_zero : j.val = 0
    · simp_all
    · specialize r_prop ⟨j - 1, by grind⟩
      grind
  · use ⟨ 0, by grind ⟩
    simp_all

theorem Vector.exists_ne_from_ne {α : Type} (n : ℕ) (l1 l2 : Vector α n):
    l1 ≠ l2 → ∃ i : Fin n, l1[i] ≠ l2[i] ∧ ∀ j : Fin i, l1[j] = l2[j] := by
  intro ineq
  apply List.exists_ne_from_ne
  · grind
  · grind
  · simp_all

theorem List.not_lex_len {α : Type} (n : ℕ) (l1 l2 : List α) (p : α → α → Prop)(len1 : l1.length = n) (len2 : l2.length = n) (x : Fin n)
(neq : ¬l1[↑x] = l2[↑x])
(prop : ∀ (x : Fin n), ¬l1[↑x] = l2[↑x] → ¬p l1[↑x] l2[↑x] → ∃ x_1 : Fin x, ¬l1[↑x_1] = l2[↑x_1]):
Lex p l1 l2 := by
  cases l1 <;> cases l2 <;> try grind -- remove tauto cases
  rename_i h1 t1 h2 t2
  have p0 := prop ⟨x,by grind⟩
  by_cases x_zero : x.val = 0
  · specialize prop ⟨0, by grind⟩
    simp_all
    apply Lex.rel
    exact prop
  · simp_all
    by_cases h12 : h1 = h2
    · subst h12
      apply Lex.cons
      apply List.not_lex_len (n := n-1) (x := ⟨ x-1, by omega⟩)
      rotate_left
      · intro x' not_eq not_p
        specialize prop ⟨x' + 1, by omega⟩ not_eq not_p
        obtain ⟨i,p⟩ := prop
        have i_ne_zero : i.val ≠ 0 := by by_contra; simp_all
        have fin_p : i.val - 1 < ↑x' := by
          have pp : i.val < x'.val + 1:= by simp_all
          omega
        use ⟨i-1, fin_p⟩
        repeat rw [List.getElem_cons] at p
        simp_all
      · grind
      · grind
      · repeat rw [List.getElem_cons] at neq
        simp_all
    · apply Lex.rel
      by_contra
      specialize prop ⟨ 0, by grind ⟩
      grind

theorem List.not_Lex {α : Type} (n : ℕ) (p : α → α → Prop) (l1 l2 : _root_.Vector α n):
  ¬(Vector.Lex n p l1 l2) →
    (∀ i : Fin n, l1[i] = l2[i]) ∨ (∃ i : Fin n, l1[i] ≠ l2[i] ∧ (¬ (p l1[i] l2[i])) ∧ ∀ j : Fin i, l1[j] = l2[j]) := by
    contrapose
    simp
    intro x neq prop
    unfold Vector.Lex
    have h : l1.toArray.size = n := by grind
    apply List.not_lex_len
    · apply neq
    · intro x' p1 p2
      specialize prop ⟨ x', by omega⟩
      simp_all
    · grind
    · grind

lemma mergeSort_head {α : Type} (le : α → α → Bool)
  (trans : ∀ (a b c : α), le a b = true → le b c = true → le a c = true)
  (total : ∀ (a b : α), (le a b || le b a) = true)
  (l : List α)
  (l_ne_nil : (l.mergeSort le) ≠ []):
  ∀ x ∈ (l.mergeSort le).tail, le ((l.mergeSort le).head l_ne_nil) x := by
    intro x x_in_l_tail
    have pw := List.pairwise_mergeSort trans total l
    let ms := (l.mergeSort le)
    have ms_eq_l_ms : ms = (l.mergeSort le) := by rfl
    rw [← ms_eq_l_ms] at pw
    let head := (l.mergeSort le).head l_ne_nil
    cases comp : ms
    · contradiction
    case cons h t =>
      rw [comp] at pw
      apply List.pairwise_cons.mp at pw
      have p := pw.1 x
      have t_eq_tail : t = (l.mergeSort le).tail := by grind
      have x_in_t : x ∈ t := by
        rw [t_eq_tail]
        exact x_in_l_tail
      specialize p x_in_t
      grind


lemma mergeSort_head_from_head {α : Type} {le : α → α → Bool}
  {trans : ∀ (a b c : α), le a b = true → le b c = true → le a c = true}
  {total : ∀ (a b : α), (le a b || le b a) = true}
  {l : List α}
  {l_ne_nil : (l.mergeSort le) ≠ []}
  {y : α}:
  (l.mergeSort le).head l_ne_nil = y →
  ∀ x ∈ (l.mergeSort le).tail, le y x := by
    intro y_eq x x_in_tail
    rw [← y_eq]
    apply mergeSort_head
    · exact trans
    · exact total
    · exact x_in_tail

lemma mergeSort_head_from_head_unsorted {α : Type} {le : α → α → Bool}
  {trans : ∀ (a b c : α), le a b = true → le b c = true → le a c = true}
  {total : ∀ (a b : α), (le a b || le b a) = true}
  {l : List α}
  {l_ne_nil : (l.mergeSort le) ≠ []}
  {y : α}:
  (l.mergeSort le).head l_ne_nil = y →
  ∀ x ∈ l, x = y ∨ le y x := by
    intro y_eq x x_in_tail
    rw [← y_eq]
    by_cases x_head : x = y
    · left ; simp_all
    · right
      apply mergeSort_head
      · exact trans
      · exact total
      · rw [←List.mem_mergeSort (le := le)] at x_in_tail
        rw [←List.cons_head_tail (l:=l.mergeSort le)] at x_in_tail
        · simp_all
        · exact l_ne_nil

lemma merge_two_prop {α : Type} (le1 : α → α → Prop) (le2 : α → α → Bool)
  (trans : ∀ (a b c : α), le2 a b = true → le2 b c = true → le2 a c = true)
  (total : ∀ (a b : α), (le2 a b || le2 b a) = true)
  (le_eq : le1 = (fun x y => le2 x y = true))
  (l : List α):
  List.Pairwise le1 (l.mergeSort le2) := by
    subst le_eq
    apply List.pairwise_mergeSort
    all_goals
      grind

lemma mergeSort_count {α : Type} [BEq α] [LawfulBEq α] {le : α → α → Bool}
  {l : List α}
  {y : α}:
  (l.mergeSort le).count y = l.count y := by
    apply List.Perm.count
    apply List.mergeSort_perm
