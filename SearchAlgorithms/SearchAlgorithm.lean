import Mathlib.Data.Bool.AllAny
import Mathlib.Data.FinEnum
import Mathlib.Data.Finset.Empty
import Mathlib.Data.List.MinMax

import Graphlib.FinEnum
import Graphlib.SearchState

namespace WeightedDiGraph

variable {V : Type} {E : Type} [FinEnum V]

-- the graph should be an explicit parameter here
abbrev search_step_function (G : WeightedDiGraph V E) (D : Type) [FValueComp D] (state_type : Type) [has_base_search_state G D state_type] :=
      V → state_type → state_type × (Option Bool)

-- def local global variable for a graph
variable {G : WeightedDiGraph V E}
variable {D : Type} [FValueComp D]
variable {T : Type} [WellFoundedRelation T]


def extract_path_to (start : V) (goal : V) (search_state : base_search_state G D)
    (goal_reached : goal ∈ search_state.visited)
    (mother_invar : search_invar_mother_is_visited search_state)
    (mother_invar_adj : search_invar_mother_is_adjacent start search_state)
    (decreasing_invar : search_invar_mother_decreasing_path_order start search_state):
      Σ' (p : G.Path start goal), (∀ v ∈ p.support, v ≠ goal → search_state.pathOrder v ≺ search_state.pathOrder goal):=
      if start_is_goal : goal = start then
        let emptyW : G.Walk start goal := start_is_goal ▸ Walk.nil
        let emptyW_nodup : emptyW.support.Nodup := by
          simp [emptyW]
          unfold Walk.support
          split
          · next u u' x w rest u_adj_v walk_is_cons =>
            simp_all
            subst start_is_goal
            simp_all only [reduceCtorEq]
          · simp

        let emptyP : G.Path start goal := ⟨ emptyW, emptyW_nodup⟩

        have order : ∀ v ∈ emptyP.support, v ≠ goal → search_state.pathOrder v ≺ search_state.pathOrder goal := by
          intro a a_in_support v_ne_goal
          unfold emptyP at a_in_support
          unfold emptyW at a_in_support
          unfold Path.support at a_in_support
          unfold Walk.support at a_in_support
          subst start_is_goal
          simp_all
        ⟨ emptyP, order ⟩
      else
        let goal_predecessor : V := search_state.mother ⟨ goal, goal_reached ⟩
        let ⟨ path_start_pre, order_proof ⟩ := -- : Path g start goal_predecessor :=
          extract_path_to start goal_predecessor search_state (by apply mother_invar) mother_invar mother_invar_adj decreasing_invar
        let pre_adj_goal : G.Adj goal_predecessor goal := mother_invar_adj ⟨ goal , goal_reached ⟩ start_is_goal
        have goal_mother_ne_goal : goal ≠ search_state.mother ⟨goal, goal_reached⟩ := by
          by_contra goal_is_mother
          have h := FValueComp.lt_irr (search_state.pathOrder goal)
          unfold search_invar_mother_decreasing_path_order at decreasing_invar
          specialize decreasing_invar ⟨goal,goal_reached⟩ start_is_goal
          nth_rw 1 [← goal_is_mother] at decreasing_invar
          contradiction

        let goal_not_visited : goal ∉ path_start_pre.support := by
          by_contra goal_is_in_support
          have h := order_proof goal goal_is_in_support goal_mother_ne_goal
          unfold goal_predecessor at h
          unfold search_invar_mother_decreasing_path_order at decreasing_invar
          specialize decreasing_invar ⟨ goal, goal_reached⟩ start_is_goal
          clear mother_invar
          simp_all
          have eq : search_state.pathOrder (search_state.mother ⟨goal, goal_reached⟩) = search_state.pathOrder goal := by
            apply FValueComp.lt_antisymm
            exact decreasing_invar
            exact h
          have g_nle_g : ¬ search_state.pathOrder goal ≺ search_state.pathOrder goal := by
            apply FValueComp.lt_irr
          nth_rw 2 [← eq] at g_nle_g
          apply absurd h g_nle_g

        let goal_path : G.Path start goal := path_start_pre.concat pre_adj_goal goal_not_visited

        let new_order_proof : ∀ v ∈ goal_path.support, v ≠ goal → search_state.pathOrder v ≺ search_state.pathOrder goal := by
          intro a a_in_support a_ne_goal
          unfold goal_path at a_in_support
          rw [Path.support_concat_is_append_at_end] at a_in_support
          simp only [Path.support, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at a_in_support
          apply a_in_support.elim
          · intro a_in_old_path
            by_cases a_old_goal : a = goal_predecessor
            · grind
            · apply FValueComp.lt_trans
              · apply order_proof a a_in_old_path
                exact a_old_goal
              · unfold goal_predecessor
                exact decreasing_invar ⟨ goal,goal_reached ⟩ start_is_goal
          · simp_all

        ⟨ goal_path, new_order_proof ⟩

termination_by FValueComp.wf.wrap (search_state.pathOrder goal)
decreasing_by
  simp_all


theorem extract_path_visited_proof_irrelevant (start : V) (s : base_search_state G D)
    (mother_invar : search_invar_mother_is_visited s)
    (mother_invar_adj : search_invar_mother_is_adjacent start s)
    (decreasing_invar : search_invar_mother_decreasing_path_order start s)
    (u v : V)
    (h : u ∈ s.visited) (h' : v ∈ s.visited)
    (u_eq_v : u = v):
    (extract_path_to start u s h mother_invar mother_invar_adj decreasing_invar).fst.val.length =
    (extract_path_to start v s h' mother_invar mother_invar_adj decreasing_invar).fst.val.length := by
    unfold extract_path_to
    unfold Walk.length
    simp_all
    by_cases v_eq_start : v = start
    all_goals
      subst u_eq_v
      try subst v_eq_start -- does not work in one case
      simp_all only

theorem search_termination_with_empty_stack_implies_goal_visited (start : V) (goal : V) (f : V)
  (theWalk : G.Walk f goal)
  (final_state : base_search_state G D)
  (f_visited : f ∈ final_state.visited)
  (final_stack_empty : final_state.stack = [])
  (on_stack_or_all_nei_visited : search_invar_on_stack_or_all_neighbours_visited final_state): goal ∈ final_state.visited := by
    cases theWalk
    · exact f_visited
    · next nextNode adj rest_walk =>
      apply search_termination_with_empty_stack_implies_goal_visited start goal nextNode rest_walk
      · unfold search_invar_on_stack_or_all_neighbours_visited at on_stack_or_all_nei_visited
        rw [final_stack_empty] at on_stack_or_all_nei_visited
        simp at on_stack_or_all_nei_visited
        apply on_stack_or_all_nei_visited f f_visited nextNode adj
      · exact final_stack_empty
      · exact on_stack_or_all_nei_visited

lemma support_of_path_visited (u v : V) (w : G.Walk u v)
    (state : base_search_state G D)
    (mother_invar : search_invar_mother_is_visited state)
    (mother_invar_adj : search_invar_mother_is_adjacent u state)
    (decreasing_invar : search_invar_mother_decreasing_path_order u state)
    (end_visited : v ∈ state.visited)
    (walk_was_extracted : w = (extract_path_to u v state end_visited mother_invar mother_invar_adj decreasing_invar).fst.val)
    :
    ∀ x ∈ w.support, x ∈ state.visited:= by
    intro x x_in_support
    unfold extract_path_to at walk_was_extracted
    simp at walk_was_extracted
    by_cases v_eq_u : v = u
    · simp_all
      unfold Walk.support at x_in_support
      split at x_in_support
      · next nil_eq_cons =>
        rename_i v_eq_u_1
        subst v_eq_u_1 walk_was_extracted
        simp_all only [Subtype.forall, ne_eq, reduceCtorEq]
      · subst walk_was_extracted
        simp_all only [Subtype.forall, ne_eq, List.mem_cons, List.not_mem_nil, or_false]
    · simp_all
      unfold Path.concat at x_in_support
      simp at x_in_support
      cases x_in_support
      · next x_in_unextended_support =>
        apply support_of_path_visited
        rotate_left
        · apply x_in_unextended_support
        · exact mother_invar
        · exact mother_invar_adj
        · exact decreasing_invar
        · apply mother_invar
        · rfl
      · next x_eq_v =>
        rw [x_eq_v]
        exact end_visited
termination_by FValueComp.wf.wrap (state.pathOrder v)
decreasing_by
  apply decreasing_invar
  apply v_eq_u

lemma run_walk_through_state_not_on_stack_yields_all_visited
  (start v : V) (v_ne_start : v ≠ start)
  (w : G.Walk start v)
  (w_support_nodup : w.support.Nodup)
  (state : base_search_state G D)
  (start_visited : search_invar_start_visited start state)
  (on_stack_or_nei_visited : search_invar_on_stack_or_all_neighbours_visited state)
  (all_not_on_stack : ∀ u ∈ w.support, u ∈ state.stack → u = v)
  :
  ∀ u ∈ w.support, u ∈ state.visited := by
    cases w
    · intro u u_in_support
      have u_eq_start : u = start := by simp_all
      rw [u_eq_start]
      apply start_visited
    · -- walk is: start -> w -> ... -> v (with potentially w = v)
      next w start_adj_w w' =>
      intro u u_in_support_w
      unfold Walk.support at u_in_support_w
      simp at u_in_support_w
      cases u_in_support_w
      · next u_eq_start =>
        rw [u_eq_start]
        apply start_visited
      · next u_in_support_w' =>
        have w'_support_nodup : w'.support.Nodup := by
            unfold Walk.support at w_support_nodup
            simp at w_support_nodup
            exact w_support_nodup.right

        by_cases v_neq_w : v ≠ w
        · apply run_walk_through_state_not_on_stack_yields_all_visited w v v_neq_w w' w'_support_nodup state
          · unfold search_invar_start_visited
            unfold search_invar_on_stack_or_all_neighbours_visited at on_stack_or_nei_visited
            have h := on_stack_or_nei_visited ⟨ start, start_visited ⟩
            cases h
            · have start_eq_v : start = v := by
                apply all_not_on_stack
                · simp!
                · next hh =>
                  exact hh
              grind
            · next hh =>
              apply hh
              exact start_adj_w
          · exact on_stack_or_nei_visited
          · intro u' u'_in_support_w' u'_in_stack
            apply all_not_on_stack
            · simp_all!
            · exact u'_in_stack
          · exact u_in_support_w'
        · simp at v_neq_w
          have supp_w'_eq_w : w'.support = [w] := by
            let w'_type : G.Walk w w := v_neq_w ▸ w'
            rw [v_neq_w] at w'
            apply Walk.nodup_and_start_eq_end_support
            · symm
              exact v_neq_w
            · apply w'_support_nodup
          rw [supp_w'_eq_w] at u_in_support_w'
          simp_all
          have nei_start := on_stack_or_nei_visited start start_visited
          cases nei_start
          · next start_in_stack =>
            simp_all
          · next all_start_nei_visited =>
            apply all_start_nei_visited
            exact start_adj_w

lemma path_has_earliest_node_on_stack (start v : V) [DecidableEq V] (p : G.Path start v)
    (state : base_search_state G D) :
    (∃ u ∈ p.support, u ∈ state.stack ∧ u ≠ v) →
    (∃ u ∈ p.support, u ∈ state.stack ∧ u ≠ v ∧ (p.support.takeWhile (· ≠ u)).all (· ∉ state.stack)) := by
  intro ⟨ u, u_in_support, u_on_stack, u_neq_v⟩
  let opt_first : Option V := p.support.find? (· ∈ state.stack)
  have opt_first_is_some : opt_first.isSome := by
    apply List.find?_isSome.mpr ; use u ; simp_all
  have support_compose : p.support = p.support.dropLast ++ [v] := by apply Walk.support_last
  use opt_first.get opt_first_is_some
  and_intros
  · apply List.get_find?_mem
  · unfold opt_first
    grind [List.get_find?_prop]
  · unfold opt_first
    apply List.find?_nodup
    · apply support_compose
    · by_contra v_in_drop_last
      have support_is_nodup : p.val.support.Nodup := p.prop
      unfold Path.support at support_compose
      rw [support_compose] at support_is_nodup
      apply List.nodup_append.mp at support_is_nodup
      have diff := support_is_nodup.right.right
      specialize diff v v_in_drop_last v
      grind
    · apply u_in_support
    · simp_all
    · simp_all
  · unfold opt_first
    grind [List.takeWhile_until_find?]

lemma run_path_through_state_yields_node_on_stack_or_all_visited_temp (start v : V)
    (v_ne_start : v ≠ start) (p : G.Path start v) (state : base_search_state G D)
    (start_visited : search_invar_start_visited start state)
    (on_stack_or_nei_visited : search_invar_on_stack_or_all_neighbours_visited state)
    : (∃ u ∈ p.support, u ∈ state.stack ∧ u ≠ v)
    ∨ (v ∈ state.visited ∧ ∀ u ∈ p.support, u ≠ v → u ∉ state.stack ∧ u ∈ state.visited) := by
  by_cases no_onstack : (∃ u ∈ p.support, u ∈ state.stack ∧ u ≠ v)
  · left; exact no_onstack
  · right
    simp at no_onstack
    have none_on_stack : ∀ u ∈ p.val.support, u ≠ v → u ∉ state.stack := by
      intro u u_in_support u_ne_v u_on_stack
      have h := no_onstack u u_in_support u_on_stack
      contradiction
    constructor
    · apply run_walk_through_state_not_on_stack_yields_all_visited start v v_ne_start p p.prop
        state start_visited on_stack_or_nei_visited (by grind) _ (Walk.goal_in_support _)
    · intro u u_insupport u_neq_v
      constructor
      · apply none_on_stack
        · exact u_insupport
        · exact u_neq_v
      · apply run_walk_through_state_not_on_stack_yields_all_visited start v v_ne_start p p.prop
          state start_visited on_stack_or_nei_visited (by grind) _ u_insupport

lemma run_path_through_state_yields_node_on_stack_or_all_visited
  [DecidableEq V]
  (start v : V) (v_ne_start : v ≠ start)
  (p : G.Path start v)
  (state : base_search_state G D)
  (start_visited : search_invar_start_visited start state)
  (on_stack_or_nei_visited : search_invar_on_stack_or_all_neighbours_visited state)
  :
  (∃ u ∈ p.support, u ∈ state.stack ∧ u ≠ v ∧ (p.support.takeWhile (· ≠ u)).all (· ∉ state.stack)) ∨
    (v ∈ state.visited ∧ ∀ u ∈ p.support, u ≠ v → u ∉ state.stack ∧ u ∈ state.visited) := by
    have h : (∃ u ∈ p.support, u ∈ state.stack ∧ u ≠ v) ∨ (v ∈ state.visited ∧ ∀ u ∈ p.support, u ≠ v → u ∉ state.stack ∧ u ∈ state.visited) := by apply run_path_through_state_yields_node_on_stack_or_all_visited_temp <;> simp_all

    cases h
    · next h =>
      left
      apply path_has_earliest_node_on_stack ; exact h
    · next h =>
      right ; exact h




-------------------------------------------------
-- Tremination metrics

def base_search_state_termination_metric
    (s : base_search_state G D): ℕ × ℕ :=
    (Fintype.card V - s.visited.card, s.stack.length)

abbrev termination_metric_decreasing_proof
   {state_type : Type} [has_base_search_state G D state_type]
  (goal : V)
  (search_step : search_step_function G D state_type)
  (termination_metric : state_type → T) :=
    ∀ s : state_type, (search_step goal s).2 = none →
    WellFoundedRelation.rel (termination_metric (search_step goal s).1) (termination_metric s)
    --    Prod.Lex (fun x1 x2 => x1 < x2) (fun x1 x2 => x1 < x2)
    --    (termination_metric (search_step goal s).1) (termination_metric s)



------------------------------------------------------------------------------------------
-- Search Recurse
------------------
variable {state_type : Type} [has_base_search_state G D state_type]
variable {goal : V}


def search_recurse
    (priorState : state_type)
    (search_step : search_step_function G D state_type)
    (termination_metric : state_type → T)
    (decreasing_proof : termination_metric_decreasing_proof goal search_step termination_metric):
    state_type × Bool :=

  let qq := search_step goal priorState
  let nextState := qq.fst
  let result : Option Bool := qq.snd
  if result_is_none : result = none then

    --let still_not_terminated : nextState.terminated = false := by
    search_recurse nextState search_step termination_metric decreasing_proof
  else ⟨ nextState, result.get (by apply Option.isSome_iff_ne_none.mpr ; exact result_is_none) ⟩
termination_by termination_metric priorState
decreasing_by
  apply decreasing_proof
  apply result_is_none



lemma search_recurse_obtain_termination_property
    (priorState : state_type)
    (search_step : search_step_function G D state_type)
    (termination_metric : state_type → T)
    (decreasing_proof : termination_metric_decreasing_proof goal search_step termination_metric)
        -- until here all necessary for calling the search_recurse
    (terminated_with : Bool) -- recursion terminated with
    (property_after_termination : state_type → Prop):
      (∀ s : state_type, (search_step goal s).2 = some terminated_with → property_after_termination (search_step goal s).1)
    →
      ((search_recurse priorState search_step termination_metric decreasing_proof).2 = terminated_with →
      property_after_termination (search_recurse priorState search_step termination_metric decreasing_proof).1):= by
      intro step_termination_property recursion_terminated_with
      unfold search_recurse at recursion_terminated_with ⊢
      simp_all
      split
      · next search_step_returned_none =>
        -- recursive case
        simp_all
        apply search_recurse_obtain_termination_property
        rotate_right
        · use terminated_with -- recursion termiantes with same result
        · apply step_termination_property
        · apply recursion_terminated_with
      · next h =>
        simp_all
        apply step_termination_property
        apply Option.eq_some_iff_get_eq.mpr
        simp_all
        apply Option.isSome_iff_ne_none.mpr
        exact h
termination_by termination_metric priorState
decreasing_by
  next step_returned_none =>
  apply decreasing_proof
  apply step_returned_none



lemma search_recurse_obtain_base_termination_property
    (goal : V)
    (priorState : state_type)
    (search_step : search_step_function G D state_type)
    (termination_metric : state_type → T)
    (decreasing_proof : termination_metric_decreasing_proof goal search_step termination_metric)
        -- until here all necessary for calling the search_recurse
    (terminated_with : Bool) -- recursion terminated with
    (property_after_termination : base_search_state G D → Prop):
      (∀ s : state_type, (search_step goal s).2 = some terminated_with → property_after_termination (has_base_search_state.to_base_state (search_step goal s).1))
    →
      ((search_recurse priorState search_step termination_metric decreasing_proof).2 = terminated_with →
      property_after_termination (has_base_search_state.to_base_state (search_recurse priorState search_step termination_metric decreasing_proof).1)) := by
      intro property_holds
      apply search_recurse_obtain_termination_property priorState search_step termination_metric decreasing_proof (terminated_with) (fun x => property_after_termination (has_base_search_state.to_base_state x)) -- fun needed to tell lean what the "invariant" is it should apply
      exact property_holds


abbrev invar_carries_over_step
    (search_step : search_step_function G D state_type)
    (invar : state_type → Prop) :=
      ∀ s : state_type, invar s → invar (search_step goal s).fst


abbrev base_invar_carries_over_step
    (search_step : search_step_function G D state_type)
    (invar : base_search_state G D → Prop) :=
      ∀ s : state_type, invar (has_base_search_state.to_base_state s) → invar (has_base_search_state.to_base_state (search_step goal s).fst)



lemma search_recurse_lift_invariant
    (priorState : state_type)
    (search_step : search_step_function G D state_type)
    (termination_metric : state_type → T)
    (decreasing_proof : termination_metric_decreasing_proof goal search_step termination_metric)
        -- until here all necessary for calling the search_recurse
    (invar : state_type → Prop):
      invar priorState ∧ (invar_carries_over_step (goal := goal) search_step invar)
         → invar (search_recurse priorState search_step termination_metric decreasing_proof).fst:= by
      intro ⟨ prior_invar, invar_carries ⟩
      unfold search_recurse
      simp_all
      split
      · next search_step_returned_none =>
        -- recursive case
        apply search_recurse_lift_invariant
        constructor
        · unfold invar_carries_over_step at invar_carries
          apply invar_carries
          exact prior_invar
        · exact invar_carries
      · next h =>
        simp_all
termination_by termination_metric priorState
decreasing_by
  next step_returned_none =>
  apply decreasing_proof
  apply step_returned_none



lemma search_recurse_lift_invariant_under_return_assumption
    (priorState : state_type)
    (search_step : search_step_function G D state_type)
    (termination_metric : state_type → T)
    (decreasing_proof : termination_metric_decreasing_proof goal search_step termination_metric)
        -- until here all necessary for calling the search_recurse
    (invar : state_type → Prop)
    (return_value : Bool):
      invar priorState ∧ (invar_carries_over_step (goal:=goal) search_step invar)
      ∧ (search_recurse priorState search_step termination_metric decreasing_proof).snd = return_value
         → invar (search_recurse priorState search_step termination_metric decreasing_proof).fst:= by
      intro ⟨ prior_invar, invar_carries, returned_value⟩
      unfold search_recurse
      simp_all
      split
      · next search_step_returned_none =>
        -- recursive case
        apply search_recurse_lift_invariant_under_return_assumption
        and_intros
        rotate_right
        · use return_value
        · unfold invar_carries_over_step at invar_carries
          apply invar_carries
          exact prior_invar
        · exact invar_carries
        · unfold search_recurse at returned_value
          simp_all
      · next h =>
        simp_all
termination_by termination_metric priorState
decreasing_by
  next step_returned_none =>
  apply decreasing_proof
  apply step_returned_none



lemma search_recurse_lift_base_invariant
    (priorState : state_type)
    (search_step : search_step_function G D state_type)
    (termination_metric : state_type → T)
    (decreasing_proof : termination_metric_decreasing_proof goal search_step termination_metric)
        -- until here all necessary for calling the search_recurse
    (invar : base_search_state G D → Prop):
      invar (has_base_search_state.to_base_state priorState)
      ∧ (base_invar_carries_over_step search_step invar (goal := goal))
         → invar (has_base_search_state.to_base_state (search_recurse priorState search_step termination_metric decreasing_proof).fst) := by
      intro ⟨invar_holds_on_base, invar_carries⟩
      apply search_recurse_lift_invariant priorState search_step termination_metric decreasing_proof (fun x => invar (has_base_search_state.to_base_state x)) -- fun needed to tell lean what the "invariant" is it should apply
      constructor
      · use invar_holds_on_base
      · use invar_carries



abbrev invar_becoming_true_causes_other_invar
    (search_step : search_step_function G D state_type)
    (invar_1 : state_type → Prop) (invar_2 : state_type → Prop) :=
      ∀ s : state_type, ¬ invar_1 s ∧ invar_1 (search_step goal s).fst → invar_2 (search_step goal s).fst



lemma search_recurse_lift_invariant_under_trigger
    (priorState : state_type)
    (search_step : search_step_function G D state_type)
    (termination_metric : state_type → T)
    (decreasing_proof : termination_metric_decreasing_proof goal search_step termination_metric)
        -- until here all necessary for calling the search_recurse
    (invar_end : state_type → Prop)
    (invar_middle : state_type → Prop):
      (¬ invar_middle (search_recurse priorState search_step termination_metric decreasing_proof).fst)
      ∧ (¬ invar_end priorState)
      ∧ (invar_carries_over_step search_step invar_middle (goal := goal))
      ∧ (invar_becoming_true_causes_other_invar search_step invar_end invar_middle (goal := goal))
      → ¬ invar_end (search_recurse priorState search_step termination_metric decreasing_proof).fst:= by
      intro ⟨ terminated_with_invar_middle_false, not_invar_end_prior, invar_middle_carries, invar_end_triggers_middle⟩

      unfold search_recurse at terminated_with_invar_middle_false ⊢
      simp_all
      split
      · simp_all
        let next_state := (search_step goal priorState).1
        by_cases invar_end next_state
        · next invar_end_becomes_true =>
          have invar_middle_becomes_true := invar_end_triggers_middle priorState ⟨not_invar_end_prior, invar_end_becomes_true ⟩
          have invar_middle_stays_true : invar_middle (search_recurse (search_step goal priorState).1 search_step termination_metric decreasing_proof).1 := by
            apply search_recurse_lift_invariant
            exact ⟨ invar_middle_becomes_true, invar_middle_carries⟩
          contradiction
        · next invar_end_not_true =>
          apply search_recurse_lift_invariant_under_trigger
          rotate_left
          · use invar_middle
          · and_intros
            · use terminated_with_invar_middle_false
            · use invar_end_not_true
            · use invar_middle_carries
            · use invar_end_triggers_middle
      · -- search step showed termination
        simp_all
        by_contra invar_end_becomes_true
        have invar_middle_becomes_true := invar_end_triggers_middle priorState ⟨not_invar_end_prior, invar_end_becomes_true ⟩
        contradiction
termination_by termination_metric priorState
decreasing_by
  next step_returned_none invar_holds =>
  apply decreasing_proof
  apply step_returned_none


section

variable {start : V}
variable {d : D}
variable {start_state : state_type}
variable {search_step : search_step_function G D state_type}
variable {termination_metric : state_type → T}




abbrev step_stack_empty_if_terminated_without_goal :=
  ∀ s : state_type,
    (search_step goal s).2 = false →
      search_prop_stack_empty (has_base_search_state.to_base_state (G:=G) (D:=D) (search_step goal s).1)

abbrev step_keeps_goal_on_stack :=
  ∀ s : state_type,
    search_prop_goal_on_stack goal (has_base_search_state.to_base_state (G:=G) (D:=D) s) →
    search_prop_goal_on_stack goal (has_base_search_state.to_base_state (G:=G) (D:=D) (search_step goal s).1)

abbrev step_goal_becomes_visited_it_is_on_stack:=
  ∀ s : state_type,
  goal ∉ (has_base_search_state.to_base_state (G:=G) (D:=D) s).visited ∧ goal ∈ (has_base_search_state.to_base_state (G:=G) (D:=D) (search_step goal s).1).visited
  → search_prop_goal_on_stack goal (has_base_search_state.to_base_state (G:=G) (D:=D) (search_step goal s).1)

abbrev search_step_terminates_when_goal_stack_head
--  (start_is_base_init : (has_base_search_state.to_base_state (g:=g) start_state) = (base_search_state_initial start))
:= (∃ tail : List V, (has_base_search_state.to_base_state (G:=G) (D:=D) start_state).stack = goal :: tail) → (search_step goal start_state).2 = some true
--:= (has_base_search_state.to_base_state (g:=g) start_state).stack = [goal] → (search_step goal start_state).2 = some true



section
variable (decreasing_proof : termination_metric_decreasing_proof goal search_step termination_metric)


def search_internal: state_type × Bool :=
    search_recurse start_state search_step termination_metric decreasing_proof

abbrev search_step_goal_on_stack_if_terminated :=
    ∀ s : state_type, ∀ goal : V, (search_step goal s).2 = true →
      goal ∈ (has_base_search_state.to_base_state (G:=G) (D:=D) (search_step goal s).1).stack


lemma search_goal_on_stack_if_returned_true
  (goal_on_stack_if_terminated : search_step_goal_on_stack_if_terminated (search_step:=search_step)):
    (search_internal (start_state:=start_state) decreasing_proof).2 = true →
      search_prop_goal_on_stack goal (has_base_search_state.to_base_state (G:=G) (D:=D) (search_internal (start_state:=start_state) decreasing_proof).1) := by
    intro terminated_with_goal_found
    unfold search_internal
    apply search_recurse_obtain_base_termination_property goal (start_state) (property_after_termination := search_prop_goal_on_stack goal) (terminated_with := true)
    · intro s
      apply goal_on_stack_if_terminated
    · exact terminated_with_goal_found



section
variable (start_is_base_init : (has_base_search_state.to_base_state (G:=G) (D:=D) start_state) = (base_search_state_initial start d))
variable (invar_carries_over_step : base_invar_carries_over_step search_step (goal:=goal) (search_invar_all_basic start))
include start_is_base_init invar_carries_over_step


lemma search_returns_with_invariants :
    search_invar_all_basic start (has_base_search_state.to_base_state (G:=G) (D:=D) (search_internal (start_state:=start_state) decreasing_proof).1) := by
    unfold search_internal
    apply search_recurse_lift_base_invariant
    constructor
    · rw [start_is_base_init]
      unfold base_search_state_initial
      simp_all
    · exact invar_carries_over_step


lemma search_returns_with_stack_visited:
    search_invar_stack_is_visited (has_base_search_state.to_base_state (G:=G) (D:=D) (search_internal (start_state:=start_state) decreasing_proof).1) := by
    have all_invars := search_returns_with_invariants decreasing_proof start_is_base_init invar_carries_over_step
    unfold search_invar_all_basic at all_invars
    exact all_invars.1


lemma search_visited_goal_if_returned_true
  (goal_on_stack_if_terminated : search_step_goal_on_stack_if_terminated (search_step:=search_step)):
  (search_internal (start_state:=start_state) decreasing_proof).2 = true → goal ∈ (has_base_search_state.to_base_state (G:=G) (D:=D) (search_internal (start_state:=start_state) decreasing_proof).1).visited := by
    intro terminated_with_goal_found
    apply search_returns_with_stack_visited
    · exact start_is_base_init
    · exact invar_carries_over_step
    · apply search_goal_on_stack_if_returned_true
      · exact goal_on_stack_if_terminated
      · exact terminated_with_goal_found


lemma search_returns_with_mother_visited:
    search_invar_mother_is_visited (has_base_search_state.to_base_state (G:=G) (D:=D) (search_internal (start_state:=start_state) decreasing_proof).1) := by
    have all_invars := search_returns_with_invariants decreasing_proof start_is_base_init invar_carries_over_step
    unfold search_invar_all_basic at all_invars
    exact all_invars.2.1

lemma search_returns_with_mother_adjacent:
    search_invar_mother_is_adjacent start (has_base_search_state.to_base_state (G:=G) (D:=D) (search_internal (start_state:=start_state) decreasing_proof).1) := by
    have all_invars := search_returns_with_invariants decreasing_proof start_is_base_init invar_carries_over_step
    unfold search_invar_all_basic at all_invars
    exact all_invars.2.2.1

lemma search_returns_with_mother_decreasing:
    search_invar_mother_decreasing_path_order start (has_base_search_state.to_base_state (G:=G) (D:=D)  (search_internal (start_state:=start_state) decreasing_proof).1) := by
    have all_invars := search_returns_with_invariants decreasing_proof start_is_base_init invar_carries_over_step
    unfold search_invar_all_basic at all_invars
    exact all_invars.2.2.2.1

lemma search_returns_with_start_visited:
    search_invar_start_visited start (has_base_search_state.to_base_state (G:=G) (D:=D) (search_internal (start_state:=start_state) decreasing_proof).1) := by
    have all_invars := search_returns_with_invariants decreasing_proof start_is_base_init invar_carries_over_step
    unfold search_invar_all_basic at all_invars
    exact all_invars.2.2.2.2.2

lemma search_returns_with_node_on_stack_or_all_neighbours_visited:
    search_invar_on_stack_or_all_neighbours_visited (has_base_search_state.to_base_state (G:=G) (D:=D) (search_internal (start_state:=start_state) decreasing_proof).1) := by
    have all_invars := search_returns_with_invariants decreasing_proof start_is_base_init invar_carries_over_step
    unfold search_invar_all_basic at all_invars
    exact all_invars.2.2.2.2.1


/-! ## Execution of search --/

def search_exe
    (goal_on_stack_if_terminated : search_step_goal_on_stack_if_terminated (search_step:=search_step)):
    Option (G.Path start goal) :=
  let ret := search_internal decreasing_proof
  let final_state:= ret.1
  let found_goal := ret.2

  if found_goal_true : found_goal = true then

    have goal_in_final_visited :=
      search_visited_goal_if_returned_true decreasing_proof start_is_base_init invar_carries_over_step goal_on_stack_if_terminated found_goal_true

    have mother_visited := search_returns_with_mother_visited decreasing_proof start_is_base_init invar_carries_over_step

    have mother_adjacent := search_returns_with_mother_adjacent decreasing_proof start_is_base_init invar_carries_over_step

    have mother_decreasing := search_returns_with_mother_decreasing decreasing_proof start_is_base_init invar_carries_over_step

    some (extract_path_to start goal (has_base_search_state.to_base_state final_state)
      goal_in_final_visited mother_visited mother_adjacent mother_decreasing).1
  else
    none

theorem search_is_sound
    (goal_on_stack_if_terminated : search_step_goal_on_stack_if_terminated (search_step:=search_step)):
    (Option.isSome (search_exe decreasing_proof start_is_base_init invar_carries_over_step goal_on_stack_if_terminated) → (∃ x : (G.Path start goal), x = x)) := by
  intro h -- Option.isSome true on some and false on none, x = x since we need a formula
  constructor -- since goal is existence
  rfl
  let w := Option.get (search_exe decreasing_proof start_is_base_init invar_carries_over_step goal_on_stack_if_terminated) -- Option.get extracts value of returned some and fails otherwise
  apply w
  simp_all

end


section
variable (stack_empty_if_terminated_without_goal : step_stack_empty_if_terminated_without_goal (search_step:=search_step) (goal:=goal))
include stack_empty_if_terminated_without_goal

lemma search_empty_stack_if_returned_false_recurse:
    (search_internal (start_state := start_state) decreasing_proof).2 = false
    → search_prop_stack_empty (has_base_search_state.to_base_state (G:=G) (D:=D) (search_internal (start_state := start_state) decreasing_proof).1) := by
    intro terminated_with_goal_not_found
    unfold search_internal
    let prop_after_termination : state_type → Prop :=
      (fun s => search_prop_stack_empty (has_base_search_state.to_base_state (G:=G) (D:=D) s))
    apply search_recurse_obtain_termination_property (state_type := state_type) (property_after_termination := prop_after_termination) (terminated_with := false)
    · intro s
      unfold prop_after_termination
      unfold step_stack_empty_if_terminated_without_goal at stack_empty_if_terminated_without_goal
      apply stack_empty_if_terminated_without_goal
    · exact terminated_with_goal_not_found


lemma search_recurse_goal_not_visited_if_terminated
    (keeps_goal_on_stack : step_keeps_goal_on_stack (search_step:=search_step) (goal:=goal))
    (goal_becomes_visited_implies_on_stack: step_goal_becomes_visited_it_is_on_stack (search_step:=search_step) (goal:=goal))
    :
    (search_internal (start_state := start_state) decreasing_proof).2 = false
    ∧ ¬ search_prop_goal_visited goal (has_base_search_state.to_base_state (G:=G) (D:=D) start_state)
    → ¬ search_prop_goal_visited goal (has_base_search_state.to_base_state (G:=G) (D:=D) (search_internal (start_state := start_state) decreasing_proof).1) := by
    intro ⟨ terminated_with_false, goal_not_visited_before ⟩
    unfold search_internal
    apply search_recurse_lift_invariant_under_trigger start_state search_step (invar_end:= fun s => search_prop_goal_visited goal (has_base_search_state.to_base_state s))
    and_intros
    rotate_right
    · use (fun s =>
        let base_state : base_search_state G D := (has_base_search_state.to_base_state s)
        search_prop_goal_on_stack goal base_state)
    · apply search_empty_stack_if_returned_false_recurse at terminated_with_false
      unfold search_prop_goal_on_stack at ⊢
      unfold search_prop_stack_empty at terminated_with_false
      unfold search_internal at terminated_with_false
      simp_all
      exact stack_empty_if_terminated_without_goal
    · apply goal_not_visited_before
    · apply keeps_goal_on_stack
    · apply goal_becomes_visited_implies_on_stack

section
variable (start_is_base_init : (has_base_search_state.to_base_state (G:=G) (D:=D) start_state) = (base_search_state_initial start d))
include start_is_base_init





lemma search_not_visited_goal_if_returned_false
    (step_terminates_if_goal_is_stack_head : search_step_terminates_when_goal_stack_head (search_step:=search_step) (goal:=goal) (start_state:=start_state))
    (keeps_goal_on_stack : step_keeps_goal_on_stack (search_step:=search_step) (goal:=goal))
    (goal_becomes_visited_implies_on_stack: step_goal_becomes_visited_it_is_on_stack (search_step:=search_step) (goal:=goal))
    :
    (search_internal (start_state := start_state) decreasing_proof).2 = false → goal ∉ (has_base_search_state.to_base_state (G:=G) (D:=D) (search_internal (start_state := start_state) decreasing_proof).1).visited := by
    --(start : V) (goal : V):
    --(dfs_internal g start goal).2 = false → goal ∉ (dfs_internal g start goal).1.visited := by
     intro terminated_with_not_goal_found
     apply search_recurse_goal_not_visited_if_terminated
     · exact stack_empty_if_terminated_without_goal
     · exact keeps_goal_on_stack
     · exact goal_becomes_visited_implies_on_stack
     constructor
     · exact terminated_with_not_goal_found
     · rw [start_is_base_init]
       unfold base_search_state_initial
       unfold search_prop_goal_visited
       simp
       by_contra goal_is_start
       unfold search_internal at terminated_with_not_goal_found
       unfold search_recurse at terminated_with_not_goal_found
       have initial_stack_is_goal : (has_base_search_state.to_base_state (G:=G) (D:=D) start_state).stack = [goal] := by
         rw [start_is_base_init]
         unfold base_search_state_initial
         simp_all
       unfold search_step_terminates_when_goal_stack_head at step_terminates_if_goal_is_stack_head
       simp_all


section
variable (invar_carries_over_step : base_invar_carries_over_step search_step (goal:=goal) (search_invar_all_basic start))
include invar_carries_over_step

theorem search_is_complete
    (goal_on_stack_if_terminated : search_step_goal_on_stack_if_terminated (search_step:=search_step))
    (keeps_goal_on_stack : step_keeps_goal_on_stack (search_step:=search_step) (goal:=goal))
    (goal_becomes_visited_implies_on_stack: step_goal_becomes_visited_it_is_on_stack (search_step:=search_step) (goal:=goal))
----
    (step_terminates_if_goal_is_stack_head : search_step_terminates_when_goal_stack_head (search_step:=search_step) (goal:=goal) (start_state:=start_state))
    :
    ((∃ x : (G.Path start goal), x = x) → Option.isSome (search_exe decreasing_proof start_is_base_init invar_carries_over_step goal_on_stack_if_terminated)) := by
    -- or Option.isNone (dfs g start goal) → ∄ x (Path g start goal), x = x
      intro path_exists
      apply Exists.elim path_exists
      intro thePath a; clear a-- uninformativ x=X

      let final := search_internal (start_state:=start_state) decreasing_proof
      let final_state : base_search_state G D := has_base_search_state.to_base_state final.1

      have start_visited : search_invar_start_visited start final_state :=
        search_returns_with_start_visited decreasing_proof start_is_base_init invar_carries_over_step
      have on_stack_or_all_nei_visited : search_invar_on_stack_or_all_neighbours_visited final_state:=
        search_returns_with_node_on_stack_or_all_neighbours_visited decreasing_proof start_is_base_init invar_carries_over_step

      by_contra terminates_with_none
      simp at terminates_with_none

      have search_returned_false : (search_internal (start_state:=start_state) decreasing_proof).2 = false := by
        unfold search_exe at terminates_with_none
        simp at terminates_with_none
        exact terminates_with_none

      have final_stack_empty : final_state.stack = [] := by
        apply search_empty_stack_if_returned_false_recurse
        · exact stack_empty_if_terminated_without_goal
        · exact search_returned_false


      have goal_not_visited : goal ∉ final_state.visited := --
        search_not_visited_goal_if_returned_false decreasing_proof stack_empty_if_terminated_without_goal start_is_base_init step_terminates_if_goal_is_stack_head keeps_goal_on_stack goal_becomes_visited_implies_on_stack search_returned_false

      obtain ⟨theWalk, nodupe ⟩ := thePath
      have goal_in_final := search_termination_with_empty_stack_implies_goal_visited start goal start theWalk final_state start_visited final_stack_empty on_stack_or_all_nei_visited
      contradiction


theorem search_is_complete_inv
    (goal_on_stack_if_terminated : search_step_goal_on_stack_if_terminated (search_step:=search_step))
    (keeps_goal_on_stack : step_keeps_goal_on_stack (search_step:=search_step) (goal:=goal))
    (goal_becomes_visited_implies_on_stack: step_goal_becomes_visited_it_is_on_stack (search_step:=search_step) (goal:=goal))
----
    (step_terminates_if_goal_is_stack_head : search_step_terminates_when_goal_stack_head (search_step:=search_step) (goal:=goal) (start_state:=start_state))
    :
    Option.isNone (search_exe decreasing_proof start_is_base_init invar_carries_over_step goal_on_stack_if_terminated) → ¬ ∃ x : (G.Path start goal), x = x := by
      intro optionIsNone
      by_contra pathExists
      have isSome := search_is_complete decreasing_proof stack_empty_if_terminated_without_goal start_is_base_init invar_carries_over_step goal_on_stack_if_terminated keeps_goal_on_stack goal_becomes_visited_implies_on_stack step_terminates_if_goal_is_stack_head
      simp_all

end

end
end
end
end
end WeightedDiGraph
