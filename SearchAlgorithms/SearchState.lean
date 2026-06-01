import Graphlib.Basic
import Init.SizeOf
import Mathlib.Data.Prod.Lex
import Mathlib.Order.Basic
import Mathlib.Algebra.Order.Kleene

/-- custom less than predicate on the type of the F-Values -/
class FValueComp (D : Type) where
  lt : D → D → Bool
  wf : WellFounded (fun x y => lt x y = true)
  lt_irr (x : D) : ¬ lt x x
  lt_trans (x y z : D) : lt x y → lt y z → lt x z
  lt_antisymm (x y : D) : lt x y → lt y x → x = y
  lt_sem_tot (x y : D) : x ≠ y → lt x y ∨ lt y x

infix:90 " ≺ " => FValueComp.lt

namespace Nat
instance : FValueComp ℕ where
  lt (x y : ℕ) : Bool := x < y
  wf := by
    simp
    apply lt_wfRel.wf
  lt_irr := by grind
  lt_trans := by grind
  lt_antisymm := by grind
  lt_sem_tot := by grind
end Nat


class SizeOfFromPreOrder (D : Type) [Preorder D] [SizeOf D] where
  comp : ∀ x y : D, x < y → sizeOf x < sizeOf y


namespace Nat
instance : SizeOfFromPreOrder ℕ where
  comp := by intro x y leq ; simp_all

@[simp] instance instSizeOfNatFin (n : ℕ) : SizeOf (ℕ × Fin n) where
  sizeOf x := x.fst * (n+1) + x.snd

instance (n : ℕ) : SizeOfFromPreOrder (ℕ × Fin n) where
  comp := by
    intro x y leq
    unfold sizeOf
    unfold instSizeOfNatFin
    apply Prod.lt_iff.mp at leq
    obtain ⟨ x1, x2⟩ := x
    obtain ⟨ y1, y2⟩ := y
    rcases leq
    · case inl ord =>
      obtain ⟨a,b⟩  := ord
      simp_all
      apply add_lt_add_of_lt_of_le
      · repeat rw [Nat.mul_succ]
        apply add_lt_add_of_le_of_lt
        · apply mul_le_mul_right
          apply le_iff_eq_or_lt.mpr
          right
          apply a
        · apply a
      · apply b
    · case inr ord =>
      obtain ⟨a,b⟩ := ord
      simp_all
      apply add_lt_add_of_le_of_lt
      · apply add_le_add
        · apply mul_le_mul_right
          apply a
        · apply a
      · apply b

end Nat







namespace WeightedDiGraph

-----------------------------------------------------------------------
------ Search state of the DFS and its invariants

structure base_search_state {V E : Type} [FinEnum V] (G : WeightedDiGraph V E) (D : Type) [FValueComp D]  where
    visited : Finset V
    pathOrder : V → D
    mother : visited → V
    stack : List V


-- type class for possible expansions later on
class has_base_search_state {V E : Type} [FinEnum V] (G : WeightedDiGraph V E) (D : Type) [FValueComp D]
    (B : Type) where
  to_base_state : B → base_search_state G D

instance {V E : Type} [FinEnum V] (G : WeightedDiGraph V E) (D : Type) [FValueComp D]:
    has_base_search_state G D (base_search_state G D) where
  to_base_state := fun x => x



--------------------------- basic properties
variable {V : Type} {E : Type} [FinEnum V] --[DecidableEq V] [DecidableEq E]
variable {G : WeightedDiGraph V E}
variable {D : Type} [FValueComp D]

@[simp]
abbrev search_prop_goal_on_stack (goal : V) (s : base_search_state G D):=
      goal ∈ s.stack

@[simp]
abbrev search_prop_goal_visited (goal : V) (s : base_search_state G D):=
      goal ∈ s.visited

@[simp]
abbrev search_prop_stack_empty (s : base_search_state G D):=
      s.stack = []

@[simp]
abbrev search_prop_stack_head_not_goal (goal : V) (s : base_search_state G D) (non_empty : ¬ search_prop_stack_empty s):=
      s.stack.head non_empty ≠ goal

@[simp]
abbrev search_prop_stack_head_is_goal (goal : V) (s : base_search_state G D):=
      s.stack.head? = some goal

@[simp]
abbrev search_invar_stack_is_visited (s : base_search_state G D):=
      ∀ x : V, x ∈ s.stack → x ∈ s.visited

@[simp]
abbrev search_invar_mother_is_visited (s : base_search_state G D):=
      ∀ x : s.visited, s.mother x ∈ s.visited

@[simp]
abbrev search_invar_mother_is_adjacent (start : V) (s : base_search_state G D):=
      ∀ x : s.visited, ↑x ≠ start → G.Adj (s.mother x) x

@[simp]
abbrev search_invar_mother_decreasing_path_order (start : V) (s : base_search_state G D) :=
      ∀ x : s.visited, ↑x ≠ start → s.pathOrder (s.mother x) ≺ s.pathOrder x

@[simp]
abbrev search_invar_on_stack_or_all_neighbours_visited (s : base_search_state G D):=
      ∀ x : s.visited, ↑x ∈ s.stack ∨ ∀ y : V, (G.Adj x y) → y ∈ s.visited

@[simp]
abbrev search_invar_start_visited (start : V) (s : base_search_state G D) :=
      start ∈ s.visited

@[simp]
abbrev search_invar_start_path_order_zero (start : V) (s : base_search_state G ℕ) :=
      s.pathOrder start = 0


@[simp]
abbrev search_invar_all_basic (start : V) (s : base_search_state G D) :=
      search_invar_stack_is_visited s
      ∧ search_invar_mother_is_visited s
      ∧ search_invar_mother_is_adjacent start s
      ∧ search_invar_mother_decreasing_path_order start s
      ∧ search_invar_on_stack_or_all_neighbours_visited s
      ∧ search_invar_start_visited start s


----------------------------------------------------------------------------------------
-- initial configuration of DFS and BFS
@[reducible]
def base_search_state_initial (start : V) (d : D): base_search_state G D :=
  let initialVisited : Finset V := ⟨ {start},  by simp ⟩
  let initialMother : initialVisited → V := fun x => start
  let initialPathOrder : V → D := fun x => d
  let initialStack : List V := [start]
  base_search_state.mk initialVisited initialPathOrder initialMother initialStack


variable (start : V) (d : D)

----- Proofs that the initial state of the DFS satisfies the invariants
@[simp]
lemma search_invar_stack_is_visited_initial:
      search_invar_stack_is_visited (G:=G) (base_search_state_initial start d) := by simp

@[simp]
lemma search_invar_mother_is_visited_initial:
      search_invar_mother_is_visited (G:=G) (base_search_state_initial start d) := by simp

@[simp]
lemma search_invar_mother_is_adjacent_initial:
      search_invar_mother_is_adjacent (G:=G) start (base_search_state_initial start d) := by
      unfold search_invar_mother_is_adjacent
      unfold base_search_state_initial
      simp

@[simp]
lemma search_invar_mother_decreasing_path_order_initial:
      search_invar_mother_decreasing_path_order (G:=G) start (base_search_state_initial start d) := by
      unfold search_invar_mother_decreasing_path_order
      unfold base_search_state_initial
      simp

@[simp]
lemma search_invar_on_stack_or_all_neighbours_visited_initial:
      search_invar_on_stack_or_all_neighbours_visited (G:=G) (base_search_state_initial start d) := by
      unfold search_invar_on_stack_or_all_neighbours_visited
      unfold base_search_state_initial
      simp

@[simp]
lemma search_invar_start_visited_initial:
      search_invar_start_visited (G:=G) start (base_search_state_initial start d) := by
      unfold search_invar_start_visited
      unfold base_search_state_initial
      simp

lemma base_search_state_initial_all_basic_invars:
    search_invar_all_basic (G:=G) start (base_search_state_initial start d) := by
      unfold search_invar_all_basic ; and_intros <;> simp


lemma visited_is_smaller_than_V (state : base_search_state G D): state.visited.card ≤ Fintype.card V := by
    apply Finset.card_le_univ

end WeightedDiGraph
