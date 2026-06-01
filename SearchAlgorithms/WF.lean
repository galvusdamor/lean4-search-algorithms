import Mathlib.Order.Defs.Unbundled
import Mathlib.Algebra.Group.WithOne.Defs
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Data.Finsupp.Defs
import Mathlib.Data.Finsupp.WellFounded
import Mathlib.Data.List.ToFinsupp

/-- Bridge from `Std.Trichotomous` to `IsTrichotomous` for decidable relations.
Can be removed after update to 4.28 as Finsupp.Lex.wellFounded' is then updated. -/
instance isTrichOfStdTrich {α : Sort*} {r : α → α → Prop} [DecidableRel r]
    [Std.Trichotomous r] : IsTrichotomous α r := by
  first
  | exact inferInstance
  | exact ⟨fun a b => by
      by_cases h1 : r a b
      · exact Or.inl h1
      · by_cases h2 : r b a
        · exact Or.inr (Or.inr h2)
        · exact Or.inr (Or.inl (Std.Trichotomous.trichotomous a b h1 h2))⟩

instance : Std.Trichotomous (· < · : ℕ → ℕ → Prop) where
  trichotomous _ _ h1 h2 := Nat.le_antisymm (Nat.not_lt.mp h2) (Nat.not_lt.mp h1)

def Fin.lt (n : ℕ) (a b : Fin n) : Prop := a.val < b.val

instance {n : ℕ} : DecidableRel (Fin.lt n) := fun a b => Nat.decLt a.val b.val

instance {n : ℕ} : Std.Trichotomous (Fin.lt n) where
  trichotomous _ _ h1 h2 := Fin.ext (Nat.le_antisymm (Nat.not_lt.mp h2) (Nat.not_lt.mp h1))

def zero_wf_rel {α : Type} (rel_a : α → α → Prop) (a b : WithZero α) : Prop :=
  match (a,b) with
  | (.none, .none) => False
  | (.none, .some _) => True
  | (.some _ ,.none) => False
  | (.some a', .some b') => rel_a a' b'

def nonZero {α : Type} [Zero α] (l : List α) := ∀ a ∈ l, a ≠ Zero.zero

def ListNonZero (α : Type) (n : ℕ) [Zero α] := {l : List α // nonZero l ∧ l.length = n}

def List.LexNonZero {α : Type} [Zero α] (n : ℕ) (r : α → α → Prop) (a b : ListNonZero α n):= List.Lex r a.val b.val

def Vector.Lex (n : ℕ) (r : α → α → Prop) (as : Vector α n) (bs : Vector α n) : Prop :=
  List.Lex r as.toArray.toList bs.toArray.toList

-- not needed ... (h : n = l.length)
private def toFinsuppFin {M : Type} [Zero M] (l : List M) (n : ℕ) [DecidablePred fun i => l.getD (↑i) 0 ≠ 0] : (Fin n) →₀ M where
  toFun i := l.getD i 0
  support := {i : Fin n | l.getD i 0 ≠ 0}
  mem_support_toFun n := by
    simp only [Ne, Finset.mem_filter, and_iff_right_iff_imp]
    contrapose
    intro n_ne_in_Fin
    apply List.getD_eq_default
    grind

-- not needed (h : n = l.length)
open Classical in
private noncomputable def list_to_finsupp {α : Type} (n : ℕ) (l : List (WithZero α)) : Finsupp (Fin n) (WithZero α) := toFinsuppFin l n


@[simp, norm_cast]
theorem List.toFinsuppFin_apply {M : Type} [Zero M] (l : List M) [DecidablePred fun i => l.getD (↑i) 0 ≠ 0] (i : Fin l.length) : (toFinsuppFin l l.length: Fin l.length → M) i = l.getD i 0 :=
  rfl

@[simp]
theorem List.toFinsuppFin_cons {n : ℕ} {M : Type} [Zero M] (a : M) (l : List M) [DecidablePred fun i => (a :: l).getD (↑i) 0 ≠ 0] [DecidablePred fun i => l.getD (↑i) 0 ≠ 0] (i : Fin (n-1)) (h : i+1 < n):
    (toFinsuppFin (a :: l) n) (⟨i+1, h⟩) = (toFinsuppFin l (n-1)) i := rfl


@[simp]
theorem List.toFinsuppFin_head {n : ℕ} {M : Type} [Zero M] (a : M) (l : List M) [DecidablePred fun i => (a :: l).getD (↑i) 0 ≠ 0] (h : 0 < n):
    (toFinsuppFin (a :: l) n) (⟨0, h⟩) = a := rfl


private noncomputable def non_zero_list_to_finsupp {α : Type} (n : ℕ) (l : ListNonZero (WithZero α) n) : Finsupp (Fin n) (WithZero α) := list_to_finsupp n l.val --l.prop.2.symm


theorem List.getElem?_after_length {α : Type u} (l : List α) (i : ℕ) (h : l.length ≤ i) :
  l[i]? = none := by
    induction l
    case nil => grind
    case cons head tail ih =>
      rw [List.getElem?_cons]
      grind

open Classical in
private lemma List.lex_and_nonZero_then_Finsupp_lex {α : Type} (n : ℕ) (wf_a : WellFoundedRelation α) (l1 l2 : List (WithZero α)) (l1z : nonZero l1) (l2z : nonZero l2)
(h1 : n = l1.length) (h2 : n = l2.length):
List.Lex (zero_wf_rel wf_a.rel) l1 l2 →
  Finsupp.Lex (Fin.lt n) (zero_wf_rel wf_a.rel) (list_to_finsupp n l1) (list_to_finsupp n l2) := by
    intro lex
    unfold Finsupp.Lex Pi.Lex
    cases lex
    case nil a l =>
      use ⟨0, by grind⟩
      and_intros
      · intro j j_lt_0
        unfold list_to_finsupp
        simp_all
      · unfold zero_wf_rel list_to_finsupp
        simp
        split
        · rename_i heq
          simp_all only [Prod.mk.injEq]
          obtain ⟨left, right⟩ := heq
          unfold nonZero at l2z
          simp_all
        · trivial
        · simp_all
        · simp_all
    case rel a_1 l_1 a_2 l_2 r =>
      use ⟨ 0, by grind ⟩
      and_intros
      · intro j j_lt_0
        unfold Fin.lt at j_lt_0
        simp_all
      · unfold zero_wf_rel list_to_finsupp
        simp
        split
        rotate_left
        · trivial
        all_goals
          rename_i heq
          simp [Prod.mk.injEq] at heq
          obtain ⟨left, right⟩ := heq
          subst left right
          exact r
    case cons a l_1 l_2 h =>
      have r : Finsupp.Lex (Fin.lt (n-1)) (zero_wf_rel wf_a.rel) (list_to_finsupp (n-1) l_1) (list_to_finsupp (n-1) l_2) := by
        apply List.lex_and_nonZero_then_Finsupp_lex
        · unfold nonZero at l1z ⊢
          simp_all
        · unfold nonZero at l2z ⊢
          simp_all
        · grind
        · grind
        · exact h
      unfold Finsupp.Lex Pi.Lex at r
      obtain ⟨i, ⟨c_1,c_2 ⟩ ⟩ := r
      use ⟨i+1, by grind⟩
      and_intros
      · intro j j_lt_i_succ
        by_cases j_gt_zero : j > ⟨ 0, by grind ⟩
        · let k : Fin (n-1) := ⟨ j-1, by grind ⟩
          have j_min_1_lt_i : Fin.lt (n-1) k i := by
            unfold Fin.lt at j_lt_i_succ ⊢
            unfold k
            simp_all
            omega
          specialize c_1 k j_min_1_lt_i
          unfold list_to_finsupp at c_1 ⊢
          let k_p_1 : Fin (n):= ⟨ k+1, by grind ⟩
          have j_k_succ : j = k_p_1 := by
            unfold k_p_1 k ; grind
          rw [j_k_succ]
          unfold k_p_1
          simp_all
        · unfold list_to_finsupp
          have j_eq_zero : j = ⟨0, by grind ⟩ := by grind
          simp_all
      · whnf
        split
        rotate_left
        · trivial
        all_goals
          rename_i heq
          simp [Prod.mk.injEq] at heq
          obtain ⟨left,right⟩ := heq
          unfold list_to_finsupp at left right c_2
          unfold zero_wf_rel at c_2
          simp_all

open Classical in
private lemma List.Finsupplex_and_nonZero_then_lex {α : Type} (n : ℕ) (wf_a : WellFoundedRelation α) (l1 l2 : List (WithZero α)) (l1z : nonZero l1) (l2z : nonZero l2)
(len1 : n = l1.length) (len2 : n = l2.length):
  Finsupp.Lex (Fin.lt n) (zero_wf_rel wf_a.rel) (list_to_finsupp n l1) (list_to_finsupp n l2) → List.Lex (zero_wf_rel wf_a.rel) l1 l2:= by
    intro lex
    unfold Finsupp.Lex Pi.Lex at lex
    obtain ⟨i, ⟨c_1, c_2⟩⟩ := lex
    by_cases n_eq_zero : n = 0
    · subst n_eq_zero
      have h := i.prop
      grind
    by_cases i_eq_zero : i = ⟨ 0, by grind ⟩
    · subst i_eq_zero
      unfold zero_wf_rel list_to_finsupp at c_2
      simp_all
      cases l1 <;> cases l2
      · simp_all
      · simp_all
      · simp_all
      · simp_all
        rename_i h1 t1 h2 t2
        split at c_2
        · simp_all
        · rename_i heq
          simp [Prod.mk.injEq] at heq
          obtain ⟨left,right⟩ := heq
          unfold nonZero at l1z
          simp_all
          have prob := l1z.1
          clear left right l1z l2z
          exfalso
          apply prob
          clear prob
          rfl
        · simp_all
        · rename_i a b heq
          simp [Prod.mk.injEq] at heq
          obtain ⟨left,right⟩ := heq
          subst left right
          apply List.Lex.rel
          unfold zero_wf_rel
          simp_all
    · have h : Nat.lt 0 i := by simp ; grind
      cases l1 <;> cases l2
      · specialize c_1 ⟨0,by grind⟩ h
        unfold list_to_finsupp at c_2
        simp_all
      · specialize c_1 ⟨0,by grind⟩ h
        unfold list_to_finsupp at c_2
        simp_all
      · rename_i head tail
        specialize c_1 ⟨0,by grind⟩ h
        clear c_2
        unfold list_to_finsupp at c_1
        simp_all
      · rename_i h1 t1 h2 t2
        have h_eq : h1 = h2 := by
          specialize c_1 ⟨0,by grind⟩ h
          unfold list_to_finsupp at c_1
          simp_all
        subst h_eq
        apply List.Lex.cons
        apply List.Finsupplex_and_nonZero_then_lex (n-1)
        · unfold nonZero at l1z ⊢
          simp_all
        · unfold nonZero at l2z ⊢
          simp_all
        · grind
        · grind
        · unfold Finsupp.Lex Pi.Lex
          use ⟨i-1, by grind ⟩
          and_intros
          · intro j j_lt_i_min_one
            let k : Fin n := ⟨ j+1, by grind ⟩
            have j_succ_lt_i : Fin.lt n k i := by unfold Fin.lt at ⊢ j_lt_i_min_one ; simp_all ; grind
            specialize c_1 k j_succ_lt_i
            unfold k at c_1
            unfold list_to_finsupp at c_1 ⊢
            simp_all
          · let k : Fin (n-1) := ⟨ i-1, by grind ⟩
            have i_eq : i = ⟨k+1, by grind ⟩ := by unfold k ; grind
            unfold list_to_finsupp at c_2 ⊢
            simp_all

private lemma List.lexNonZero_then_Finsupp_lex {α : Type} (n : ℕ) (wf_a : WellFoundedRelation α) (l1 l2 : ListNonZero (WithZero α) n):
List.LexNonZero n (zero_wf_rel wf_a.rel) l1 l2 →
  Finsupp.Lex (Fin.lt n) (zero_wf_rel wf_a.rel) (non_zero_list_to_finsupp n l1) (non_zero_list_to_finsupp n l2) := by
    unfold List.LexNonZero non_zero_list_to_finsupp
    apply List.lex_and_nonZero_then_Finsupp_lex
    · exact l1.prop.1
    · exact l2.prop.1
    · grind
    · grind

private lemma List.Finsupp_lex_then_lexNonZero {α : Type} (n : ℕ) (wf_a : WellFoundedRelation α) (l1 l2 : ListNonZero (WithZero α) n):
  Finsupp.Lex (Fin.lt n) (zero_wf_rel wf_a.rel) (non_zero_list_to_finsupp n l1) (non_zero_list_to_finsupp n l2) →
List.LexNonZero n (zero_wf_rel wf_a.rel) l1 l2  := by
    unfold List.LexNonZero non_zero_list_to_finsupp
    apply List.Finsupplex_and_nonZero_then_lex
    · exact l1.prop.1
    · exact l2.prop.1
    · grind
    · grind

theorem WithZero.Acc.none {α : Type} (wf_a : WellFoundedRelation α) : Acc (zero_wf_rel (WellFoundedRelation.rel : α → α → Prop)) .none := by
    apply Acc.intro
    intro y rel
    by_contra
    unfold zero_wf_rel at rel
    clear this
    split at rel <;> simp_all

theorem WithZero.Acc.some {α : Type} (wf_a : WellFoundedRelation α) (a : α) : Acc (zero_wf_rel WellFoundedRelation.rel) (.some a) := by
  apply Acc.intro
  intro y rel
  unfold zero_wf_rel at rel
  split at rel
  · simp_all
  · simp_all; apply WithZero.Acc.none
  · simp_all
  · rename_i x xx xxx compose
    simp_all
    obtain ⟨l,r⟩ := compose
    subst l
    apply WithZero.Acc.some
termination_by wf_a.wf.wrap a
decreasing_by
  rename_i a_1 rel_1 a' b' h heq
  subst l
  simp_all only [WellFounded.val_wrap]
  have h : a = b' := by grind
  rw [h]
  exact rel

theorem WithZero.Acc {α : Type} (wf_a : WellFoundedRelation α) (a : WithZero α) : Acc (zero_wf_rel WellFoundedRelation.rel) a := by
  cases a
  · apply WithZero.Acc.none
  · apply Acc.intro
    intro y rel
    unfold zero_wf_rel at rel
    split at rel
    · simp_all
    · simp_all; apply WithZero.Acc.none
    · simp_all
    · simp_all; apply WithZero.Acc.some

theorem wf_with_zero {α : Type} (wf_a : WellFoundedRelation α) : WellFounded (zero_wf_rel wf_a.rel) := by
  apply WellFounded.intro
  intro a
  apply WithZero.Acc

theorem Fin.gt.is_wf {n : ℕ} : WellFounded (Function.swap (Fin.lt n)) := by
  apply WellFounded.intro
  apply WellFoundedGT.apply

theorem wf_list_with_zero {α : Type} (n : ℕ) (wf_a : WellFoundedRelation α) : WellFounded (List.LexNonZero n (zero_wf_rel wf_a.rel)) := by
  have finsupp_lex_wf : WellFounded (Finsupp.Lex (Fin.lt n) (zero_wf_rel wf_a.rel)) := by
    apply Finsupp.Lex.wellFounded'
    · intro n
      unfold zero_wf_rel
      split
      · grind
      · rename_i heq
        simp [Prod.mk.injEq] at heq
      · grind
      · rename_i heq
        simp [Prod.mk.injEq] at heq
    · apply wf_with_zero
    · exact Fin.gt.is_wf
  have h := InvImage.wf (non_zero_list_to_finsupp n) (finsupp_lex_wf)
  convert h
  unfold InvImage
  ext l1 l2
  constructor
  · apply List.lexNonZero_then_Finsupp_lex
  · apply List.Finsupp_lex_then_lexNonZero

private def zero_remove {α : Type} {n : ℕ}(l : Vector α n) : ListNonZero (WithZero α) n :=
  let l_0 : List (WithZero α) := l.toArray.toList.map (.some ·)
  have p_0 : nonZero l_0 := by
    unfold nonZero l_0
    intro a in_map
    apply List.mem_map.mp at in_map
    obtain ⟨ _, ⟨ _, p ⟩ ⟩ := in_map
    rw [← p]
    unfold Zero.zero
    unfold WithZero.instZero
    simp
  ⟨l_0, p_0, by grind⟩

private lemma Vector.lex_toList_non_zero_lex {α : Type} (n : ℕ) (wf_a : WellFoundedRelation α) (l1 l2 : List α)
  (lex : List.Lex WellFoundedRelation.rel l1 l2)
  (p1 : nonZero ((List.map (fun x => some x) l1) : List (WithZero α)) ∧ (List.map (fun x => some x) l1).length = n)
  (p2 : nonZero ((List.map (fun x => some x) l2) : List (WithZero α)) ∧ (List.map (fun x => some x) l2).length = n)
  :
  List.LexNonZero n (zero_wf_rel wf_a.rel) ⟨List.map (fun x => some x) l1, p1⟩ ⟨List.map (fun x => some x) l2, p2⟩ := by
    cases l1 <;> cases l2
    · cases lex
    · cases lex
      unfold List.LexNonZero
      apply List.Lex.nil
    · cases lex
    · cases lex
      · unfold List.LexNonZero
        apply List.Lex.rel
        unfold zero_wf_rel
        grind
      · unfold List.LexNonZero
        apply List.Lex.cons
        apply Vector.lex_toList_non_zero_lex (n := n-1)
        · grind
        · and_intros
          · obtain ⟨r,l⟩ := p1
            unfold nonZero at r ⊢
            grind
          · grind
        · and_intros
          · obtain ⟨r,l⟩ := p2
            unfold nonZero at r ⊢
            grind
          · grind

private lemma List.non_zero_lex_to_vector_lex {α : Type} (n : ℕ) (wf_a : WellFoundedRelation α) (l1 l2 : List α)
  (p1 : nonZero ((List.map (fun x => some x) l1) : List (WithZero α)) ∧ (List.map (fun x => some x) l1).length = n)
  (p2 : nonZero ((List.map (fun x => some x) l2) : List (WithZero α)) ∧ (List.map (fun x => some x) l2).length = n)
  (lex : List.LexNonZero n (zero_wf_rel wf_a.rel) ⟨List.map (fun x => some x) l1, p1⟩ ⟨List.map (fun x => some x) l2, p2⟩)
  :
  List.Lex WellFoundedRelation.rel l1 l2 := by
    unfold LexNonZero at lex
    cases l1 <;> cases l2
    · simp_all
    · simp_all
    · simp_all
    · simp_all
      cases lex
      case rel h =>
        apply List.Lex.rel
        unfold zero_wf_rel at h
        grind
      case cons h =>
        apply List.Lex.cons
        apply List.non_zero_lex_to_vector_lex
        · unfold LexNonZero
          apply h
        · use n-1
        · and_intros
          · obtain ⟨r,l⟩ := p1
            unfold nonZero at r ⊢
            grind
          · grind

        · and_intros
          · obtain ⟨r,l⟩ := p2
            unfold nonZero at r ⊢
            grind
          · grind

theorem wf_list {α : Type} (n : ℕ) (wf_a : WellFoundedRelation α) : WellFounded (Vector.Lex n wf_a.rel) := by
  have list_wf : WellFounded (List.LexNonZero n (zero_wf_rel wf_a.rel)) := wf_list_with_zero n wf_a
  convert InvImage.wf (zero_remove) list_wf
  ext l1 l2
  constructor
  · intro lex
    unfold zero_remove
    simp
    apply Vector.lex_toList_non_zero_lex
    exact lex
  · intro lex
    unfold Vector.Lex at lex
    unfold zero_remove at lex
    simp_all
    apply List.non_zero_lex_to_vector_lex
    exact lex

def withTop.lex {α : Type} (rel_a : α → α → Prop)  (a b : WithTop α) :=
  match (a,b) with
  | (.none, .none) => False
  | (.none, .some _) => False
  | (.some _ ,.none) => True
  | (.some a', .some b') => rel_a a' b'

theorem with_top_acc.some {α : Type} (wf_a : WellFoundedRelation α) (a : α):
   Acc (withTop.lex wf_a.rel) (.some a) := by
   apply Acc.intro
   intro y rel
   unfold withTop.lex at rel
   split at rel
   · simp_all
   · simp_all
   · rename_i x val heq
     simp [Prod.mk.injEq] at heq
     obtain ⟨r,l⟩ := heq
     unfold WithTop WithTop.some at l
     simp_all
   · rename_i x a' b' heq
     simp [Prod.mk.injEq] at heq
     obtain ⟨r,l⟩ := heq
     subst r
     have h := wf_a.wf
     apply with_top_acc.some
termination_by wf_a.wf.wrap a
decreasing_by
  · rename_i val h' a' a'' heq h''
    subst r
    simp_all only [WellFounded.val_wrap]
    unfold withTop.lex at h'
    split at h'
    · simp_all
    · simp_all
    · simp_all
    · rename_i x a''' b' heq
      simp [Prod.mk.injEq] at heq
      obtain ⟨r,l⟩ := heq
      have h1 : a' = a''' := by grind
      have h2 : a'' = b' := by grind
      have h3 : a'' = a := by
        rename_i l'
        unfold WithTop WithTop.some at l'
        grind
      subst h1 h2 h3
      exact h'

theorem with_top_acc.none {α : Type} (wf_a : WellFoundedRelation α):
   Acc (withTop.lex wf_a.rel) .none := by
   apply Acc.intro
   intro y rel
   unfold withTop.lex at rel
   split at rel
   · grind
   · grind
   · rename_i heq
     simp [Prod.mk.injEq] at heq
     subst heq
     apply with_top_acc.some
   · grind

theorem wf_with_top {α : Type} (wf_a : WellFoundedRelation α) : WellFounded (withTop.lex wf_a.rel) := by
  apply WellFounded.intro
  intro a
  cases a
  · apply with_top_acc.none
  · apply with_top_acc.some

instance : IsWellFounded ℕ Nat.lt where
  wf := Nat.lt_wfRel.wf

instance : WellFoundedRelation (WithTop (ℕ × ℕ)):=
  WellFoundedRelation.mk (withTop.lex (Prod.Lex Nat.lt Nat.lt))
    (wf_with_top (WellFoundedRelation.mk (Prod.Lex Nat.lt Nat.lt)
      (Prod.instWellFoundedRelation (α := ℕ) (β := ℕ)).wf))

instance : WellFoundedRelation (WithTop (ℕ)):=
  WellFoundedRelation.mk (withTop.lex Nat.lt)
    (wf_with_top inferInstance)

instance (n : ℕ) : WellFoundedRelation (Vector (WithTop (ℕ × ℕ)) n) :=
  WellFoundedRelation.mk (Vector.Lex n (withTop.lex (Prod.Lex Nat.lt Nat.lt)))
    (wf_list n inferInstance)

instance wf_vector_n_with_top (n : ℕ) : WellFoundedRelation (Vector (WithTop (ℕ)) n) :=
  WellFoundedRelation.mk (Vector.Lex n (withTop.lex Nat.lt)) (wf_list n inferInstance)

instance (priority:=high) (n : ℕ) : WellFoundedRelation ((Vector (WithTop (ℕ × ℕ)) n) × ℕ) :=
  WellFoundedRelation.mk (Prod.Lex (Vector.Lex n (withTop.lex (Prod.Lex Nat.lt Nat.lt))) Nat.lt)
      (Prod.instWellFoundedRelation (α := (Vector (WithTop (ℕ × ℕ)) n)) (β := ℕ)).wf
