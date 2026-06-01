import Graphlib.NatGraph
import Graphlib.SearchStep

-- def local global variable for a graph
variable {V : Type} [FinEnum V] [DecidableEq V]
variable {g : NatGraph V}


namespace Nat

@[simp]
def FValueLT (x y : ℕ × ℕ) : Bool := Prod.Lex (· < ·) (· < ·) x y

instance : FValueComp (ℕ × ℕ) where
  lt := FValueLT
  wf := by
    unfold FValueLT
    simp only [decide_eq_true_eq]
    apply Prod.Lex.instWellFoundedLTLex.wf
  lt_irr := by unfold FValueLT ; grind
  lt_trans := by unfold FValueLT ; grind
  lt_antisymm := by unfold FValueLT ; grind
  lt_sem_tot := by unfold FValueLT ; grind

end Nat


namespace NatGraph

open WeightedDiGraph


lemma hsearch_merge_trans [FValueComp (ℕ×ℕ)] (a b c : ℕ × ℕ)
  (a_b : a = b || FValueComp.lt a b)
  (b_c : b = c || FValueComp.lt b c) :
  a = c || FValueComp.lt a c := by
  by_cases a_eq_b : a = b <;> by_cases b_eq_c : b = c
  · simp_all
  · simp_all
  · simp_all
  · simp_all
    right
    apply FValueComp.lt_trans
    · exact a_b
    · exact b_c

lemma hsearch_merge_total [FValueComp (ℕ×ℕ)] (a b: ℕ × ℕ):
  (a = b || FValueComp.lt a b) || (b = a || FValueComp.lt b a) := by
  by_cases a_eq_b : a = b
  · grind
  · simp_all
    have h := FValueComp.lt_sem_tot a b a_eq_b
    cases h
    case neg.inl f => left ; exact f
    case neg.inr f => right ; right ; exact f



-----------------------------------------------------------------------
------ astar implementation and proof ------


--abbrev hsearch_search_state (g : NatGraph V) := WeightedDiGraph.base_search_state g (ℕ × Fin g.nodeNum)
abbrev hsearch_search_state (g : NatGraph V) := WeightedDiGraph.base_search_state g (ℕ × ℕ)


@[simp]
def path_val (priorState : hsearch_search_state g) (cur v : V) (adj : g.Adj cur v) : (ℕ × ℕ) :=
  ⟨ (priorState.pathOrder cur).fst + g.edgeCost adj, (priorState.pathOrder cur).snd + 1⟩

@[simp]
def new_cost (priorState : hsearch_search_state g) (cur v : V) (adj : g.Adj cur v) :=
  if (priorState.pathOrder v).1 < (path_val priorState cur v adj).1 then
    (priorState.pathOrder v)
  else if (priorState.pathOrder v).1 = (path_val priorState cur v adj).1 ∧ (priorState.pathOrder v).2 < (path_val priorState cur v adj).2 then
    (priorState.pathOrder v)
  else
    (path_val priorState cur v adj)

@[simp]
def add_heur (v : V) (p : ℕ × ℕ) (heur : V → ℕ) : ℕ × ℕ := ⟨p.1 + heur v, p.2⟩

def hsearch_step_expand
    (heur : V → ℕ)
    (priorState : hsearch_search_state g)
    (stackHead : V)
    (stackTail : List V):
    (hsearch_search_state g) :=
      -- all neighbours that either are *not visited yet* or are not on stack (to avoid dupliactes) and have shorter path via stackHead
      let newly_visited : Finset V := (Finset.univ).filterMap
        (λ v => if h : @decide (g.Adj stackHead v) (g.instDecAdj stackHead v) then
            let adj : g.Adj stackHead v := by simp_all only [decide_eq_true_eq]
            if v ∉ priorState.visited ∨
              (v ∈ priorState.visited ∧ v ∉ stackTail ∧ (priorState.pathOrder v).fst > (priorState.pathOrder stackHead).fst + g.edgeCost adj) then some v else none else none)
        (by intro a a' b a_1 a_2; simp_all) -- filter neighbors to expand the visited list

      let vList : List V := (FinEnum.toList (Finset.univ : Finset V))
      let newly_visited_list : List V := vList.filterMap (λ v => if v ∈ newly_visited then some v else none)
      let new_visited : Finset V := priorState.visited ∪ newly_visited


      let new_order : V → ℕ × ℕ := fun v  =>
        if h : @decide (g.Adj stackHead v) (g.instDecAdj stackHead v) then
          let adj : g.Adj stackHead v := by simp_all only [decide_eq_true_eq]
          if (v ∉ priorState.visited) then path_val priorState stackHead v adj
          else new_cost priorState stackHead v adj
        else priorState.pathOrder v


      let new_mother : new_visited → V := fun ⟨v, hv⟩  =>
        if not_visited_before : (v ∉ priorState.visited) then
          stackHead
        else
          if priorState.pathOrder v = new_order v then
            priorState.mother ⟨v, by simp_all⟩
          else
            stackHead

     let new_stack : List V := (stackTail ++ newly_visited_list).mergeSort (fun a b =>
        add_heur a (new_order a) heur = add_heur b (new_order b) heur || FValueComp.lt (add_heur a (new_order a) heur) (add_heur b (new_order b) heur))

     WeightedDiGraph.base_search_state.mk new_visited new_order new_mother new_stack


def hsearch_termination_metric
    (s : hsearch_search_state g): (Vector (WithTop (ℕ × ℕ)) g.nodeNum) × ℕ :=
    let l := (FinEnum.toList (Finset.univ : Finset V)).map  (fun v =>
      if v ∈ s.visited then WithTop.some (s.pathOrder v) else ⊤)

    let a := Array.mk l
    let v := Vector.mk a (by
      unfold WeightedDiGraph.nodeNum a l
      simp
      apply FinEnum.len_toList (α := V)
    )

    (v , s.stack.length)

--set_option trace.Meta.synthInstance true
--set_option pp.all true

variable (heur : V → ℕ)


section
variable (state : WeightedDiGraph.base_search_state g (ℕ×ℕ))


/-
PROBLEM
After expansion, pathOrder.1 can only stay or decrease for previously visited nodes.

PROVIDED SOLUTION
For v ∈ state.visited: In hsearch_step_expand, new_order for v is:
- If adj(head, v): if v ∉ visited then path_val else new_cost = min(old, path_val)
  Since v ∈ state.visited, we use new_cost which is ≤ old by construction (it takes the min).
- If not adj(head, v): pathOrder stays the same.
So new_pathOrder(v).1 ≤ old_pathOrder(v).1.

In new_cost:
- if old.1 < path_val.1: keep old → new = old. ≤ holds.
- if old.1 = path_val.1 ∧ old.2 < path_val.2: keep old → ≤ holds.
- else: use path_val. Since we're in the else case, old.1 ≥ path_val.1. So path_val.1 ≤ old.1. ≤ holds.

After unfolding hsearch_step_expand and new_cost, this becomes a decidable comparison. For each neighbor v of head that is visited, new_cost takes the minimum of old and path_val, so new.1 ≤ old.1. For non-neighbors, pathOrder stays the same. The goal should be provable by splitting on all the if-then-else conditions (whether v is adjacent to head, whether v is visited, etc.) and using omega or le_refl for each case. Try simp with split, omega, or decide.
-/
lemma pathOrder_mono_after_expand :
    ∀ head : V, ∀ tail : List V,
      ∀ v : V, v ∈ state.visited →
        ((hsearch_step_expand heur state head tail).pathOrder v).1 ≤ (state.pathOrder v).1 := by
  unfold hsearch_step_expand;
  unfold new_cost
  grind

/-
PROBLEM
If v is in the new visited set but not the old, then head is adjacent to v.

PROVIDED SOLUTION
Unfold hsearch_step_expand at hv. The visited set is state.visited ∪ newly_visited. Since v ∉ state.visited, v ∈ newly_visited. By definition of newly_visited = Finset.filterMap ..., v must satisfy the condition that adj(head, v) exists. Extract this adjacency.

After unfolding hsearch_step_expand at hv, v is in the union of state.visited and newly_visited. Since hv_old says v is not in state.visited, v must be in newly_visited. The newly_visited set is a Finset.filterMap over adjacencies of head. So there exists an adjacency adj : g.Adj head v. Try simp_all or Finset membership lemmas.
-/
lemma newly_visited_adj_head
    (v : V) (hv : v ∈ (hsearch_step_expand heur state head tail).visited)
    (hv_old : v ∉ state.visited) :
    g.Adj head v := by
  unfold hsearch_step_expand at hv
  contrapose! hv
  grind

/-
PROBLEM
For a newly visited node v (not in old visited), pathOrder(v).1 = pathOrder(head).1 + edgeCost.

PROVIDED SOLUTION
Unfold hsearch_step_expand. The new pathOrder for v is: if adj(head, v) then (if v ∉ state.visited then path_val else new_cost). Since hv_old : v ∉ state.visited, we use path_val. path_val = (pathOrder(head).1 + edgeCost adj, pathOrder(head).2 + 1). So the .1 component is pathOrder(head).1 + edgeCost adj.

Key: we have adj : g.Adj head v, so the decidable adj check resolves to true. And v ∉ state.visited from hv_old, so we take the path_val branch.

After unfolding hsearch_step_expand, the new pathOrder for v: since v is not in state.visited (hv_old) and adj(head, v) exists, the path_val branch is taken, giving pathOrder(head).1 + edgeCost. Try simp_all or split on conditions and use omega.
-/
lemma pathOrder_newly_visited
    (v : V) (adj : g.Adj head v)
    (hv_old : v ∉ state.visited) :
    ((hsearch_step_expand heur state head tail).pathOrder v).1 = (state.pathOrder head).1 + g.edgeCost adj := by
  unfold hsearch_step_expand;
  unfold path_val; grind

end

lemma hsearch_expand_metric_reduction : WeightedDiGraph.termination_proof_for_expand (G:=g) (state_type := hsearch_search_state g) (D:=ℕ ×ℕ) (hsearch_step_expand heur) goal hsearch_termination_metric := by
    unfold WeightedDiGraph.termination_proof_for_expand
    intro state head tail ⟨head_ne_goal,compose⟩
    unfold WellFoundedRelation.rel
    unfold instWellFoundedRelationProdVectorWithTopNat_graphlib
    apply Prod.lex_iff.mpr
    apply (Classical.or_iff_not_imp_left).mpr
    contrapose
    rw [not_and]
    intro x
    by_cases eq : (hsearch_termination_metric (hsearch_step_expand heur state head tail)).1 = (hsearch_termination_metric state).1
    · specialize x eq
      unfold hsearch_termination_metric hsearch_step_expand at x
      simp_all
      have stack_len : state.stack.length = tail.length + 1 := by
        clear eq x
        unfold WeightedDiGraph.has_base_search_state.to_base_state at compose
        unfold WeightedDiGraph.instHas_base_search_stateBase_search_state at compose
        simp only at compose
        grind
      rw [stack_len] at x
      simp at x
      apply List.exists_mem_of_length_pos at x
      simp at x
      obtain ⟨v,⟨adj_head_v, prop_v⟩⟩ := x
      unfold hsearch_step_expand hsearch_termination_metric at eq
      simp at eq
      specialize eq v
      cases prop_v
      · simp_all
      · simp_all
        rename_i h
        obtain ⟨v_visi,v_not_in_tail, cost_update ⟩ := h
        specialize eq (le_of_lt cost_update)
        apply imp_iff_or_not.mp at eq
        cases eq <;> grind
    · clear x
      apply Vector.exists_ne_from_ne at eq
      obtain ⟨ i, prop_i ⟩ := eq
      by_contra not_lex
      apply List.not_Lex at not_lex
      cases not_lex
      case neg.inl all =>
        specialize all i
        grind
      case neg.inr pos =>
        clear i prop_i
        obtain ⟨i', ⟨ not_eq, not_lex, r⟩ ⟩ := pos
        clear r
        unfold hsearch_termination_metric hsearch_step_expand at not_lex not_eq
        unfold withTop.lex at not_lex
        simp at not_lex
        simp at not_eq
        have get_helper : i'.val < (FinEnum.toList (Finset.univ : Finset V)).length := by
          clear not_lex not_eq
          unfold WeightedDiGraph.nodeNum at i'
          convert i'.prop
          apply FinEnum.len_toList
        --
        split at not_eq
        · split at not_eq
          · split at not_eq
            · split at not_eq
              · simp at not_eq
              · simp_all
                split at not_lex
                · grind
                · rename_i h h' h''
                  obtain ⟨l,r⟩ := not_eq
                  simp at h''
                  apply imp_iff_or_not.mp at h''
                  cases h''
                  all_goals
                    next h''' =>
                    rw [Prod.lex_iff] at not_lex
                    simp only [Nat.lt_eq] at not_lex
                    grind
            · simp_all
          · split at not_eq <;> simp_all
        · split at not_eq
          · next h h' =>
            apply Finset.notMem_union.mp at h
            obtain ⟨ not_in, r ⟩ := h
            clear not_lex not_eq r
            simp_all
          · grind




lemma hsearch_expand_newly_added_are_adjacent
    (priorState : hsearch_search_state g)
    (stackHead : V)
    (stackTail : List V):
    ∀ x : V, x ∉ priorState.visited ∧ x ∉ stackTail ∧
      x ∈ (hsearch_step_expand heur priorState stackHead stackTail).stack →
      g.Adj stackHead x := by
    intro x ⟨x_not_visi, ⟨ x_not_on_stack_before, x_on_stack_after ⟩  ⟩
    unfold hsearch_step_expand at x_on_stack_after
    simp_all


lemma hsearch_expand_keeps_stack_in_visited
    (priorState : hsearch_search_state  g)
    (stackHead : V)
    (stackTail : List V):
    WeightedDiGraph.search_invar_stack_is_visited priorState ∧
      stackHead ∈ priorState.visited ∧ (∀ x : V, x ∉ priorState.visited → x ∉ stackTail) →
      WeightedDiGraph.search_invar_stack_is_visited (hsearch_step_expand heur priorState stackHead stackTail) := by
      intro ⟨ stack_is_visited_prior, stackhead_visited, x_not_in_stack_tail⟩
      unfold WeightedDiGraph.search_invar_stack_is_visited
      intro x x_now_on_stack
      unfold hsearch_step_expand
      simp_all
      by_cases x_was_visited : x ∈ priorState.visited
      · left
        exact x_was_visited
      · right
        have adj : g.Adj stackHead x := by
          apply (hsearch_expand_newly_added_are_adjacent heur priorState stackHead stackTail)
          simp_all
        use adj ; left ; exact x_was_visited


lemma hsearch_expand_keeps_mother_in_visited
    (priorState : hsearch_search_state  g)
    (stackHead : V)
    (stackTail : List V):
    WeightedDiGraph.search_invar_mother_is_visited priorState ∧ stackHead ∈ priorState.visited → WeightedDiGraph.search_invar_mother_is_visited (hsearch_step_expand heur priorState stackHead stackTail) := by
      intro mother_is_visited_prior
      unfold WeightedDiGraph.search_invar_mother_is_visited
      intro x
      by_cases mother_becomes_head : (hsearch_step_expand heur priorState stackHead stackTail).mother x = stackHead
      · rw [mother_becomes_head]
        unfold hsearch_step_expand
        simp_all
      · have x_was_visited : x.val ∈ priorState.visited := by
          obtain ⟨ x', x_now_visi ⟩ := x
          unfold hsearch_step_expand at mother_becomes_head x_now_visi
          simp at x_now_visi
          cases x_now_visi
          · simp_all
          · simp_all
            rename_i h
            obtain ⟨ adj, p ⟩ := h
            cases p <;> simp_all
        have mother_unchanged :
          (hsearch_step_expand heur priorState stackHead stackTail).mother x = priorState.mother ⟨ x.val, x_was_visited ⟩ := by
          unfold hsearch_step_expand at mother_becomes_head ⊢
          simp_all
        rw [mother_unchanged]
        unfold hsearch_step_expand
        simp_all


lemma hsearch_expand_keeps_mother_is_adjacent
    (start : V)
    (priorState : hsearch_search_state  g)
    (stackHead : V)
    (stackTail : List V):
    WeightedDiGraph.search_invar_mother_is_adjacent start priorState → WeightedDiGraph.search_invar_mother_is_adjacent start (hsearch_step_expand heur priorState stackHead stackTail) := by
      intro mother_is_adjacent_prior
      unfold WeightedDiGraph.search_invar_mother_is_adjacent
      intro x
      simp_all
      intro x_not_start
      unfold hsearch_step_expand
      simp_all
      split
      next adj_decide_true =>
        split <;> split <;> grind
      · next x_not_prior_visited =>
        obtain ⟨ xx, x_in_new_visited ⟩ := x
        unfold hsearch_step_expand at x_in_new_visited
        simp at x_in_new_visited
        simp_all

lemma hsearch_mother_options
    (priorState : hsearch_search_state  g)
    (stackHead : V)
    (stackTail : List V)
    (x : priorState.visited)
    (x_still_visited : x.val ∈ (hsearch_step_expand heur priorState stackHead stackTail).visited):
      ((hsearch_step_expand heur priorState stackHead stackTail).mother ⟨x.val, x_still_visited⟩) = stackHead ∨
      (((hsearch_step_expand heur priorState stackHead stackTail).mother ⟨x.val, x_still_visited⟩) = (priorState.mother x) ∧ (priorState.mother x) ≠ stackHead)
      := by
        unfold hsearch_step_expand
        grind

set_option maxHeartbeats 1000000 in
/-- TODO: externalise haves into helper theorems -/
lemma hsearch_expand_keeps_mother_ordered
    (start : V)
    (priorState : hsearch_search_state  g)
    (stackHead : V)
    (stackTail : List V):
    WeightedDiGraph.search_invar_mother_is_visited priorState ∧
      stackHead ∈ priorState.visited ∧
      WeightedDiGraph.search_invar_mother_decreasing_path_order start priorState
      ∧ WeightedDiGraph.search_invar_mother_is_visited priorState
      → WeightedDiGraph.search_invar_mother_decreasing_path_order start
          (hsearch_step_expand heur priorState stackHead stackTail)
          := by
    intro ⟨mother_is_visited, stack_head_visited_prior, ⟨ mother_decreasing_prior, mother_visited⟩ ⟩
    unfold WeightedDiGraph.search_invar_mother_decreasing_path_order
    intro a a_not_start
    obtain ⟨a,a_now_visited⟩ := a
    unfold FValueComp.lt
    unfold Nat.instFValueCompProd
    --apply toBoolUsing_eq_true
    simp only [Nat.FValueLT, decide_eq_true_eq]
    apply Prod.lex_def.mpr
    apply Classical.or_iff_not_imp_left.mpr
    intro first_dim
    simp at first_dim


    -- local helper theorem
    have a_ne_visi_head_adj_a : a ∉ priorState.visited → g.Adj stackHead a := by
      intro a_not_visited
      unfold hsearch_step_expand at a_now_visited
      grind

    have was_visited_if_not_adj :
      ∀ x ∈ (hsearch_step_expand heur priorState stackHead stackTail).visited, ¬ g.Adj stackHead x → x ∈ priorState.visited := by
      intro x now_visited not_adj
      unfold hsearch_step_expand at now_visited
      grind

    have h_order : ∀ x : V, ¬ g.Adj stackHead x → priorState.pathOrder x = (hsearch_step_expand heur priorState stackHead stackTail).pathOrder x := by
      intro x ne_adj_head
      unfold hsearch_step_expand
      grind

    have h_mother : ∀ x : (hsearch_step_expand heur priorState stackHead stackTail).visited, ∀ ne_adj : ¬ g.Adj stackHead x, priorState.mother ⟨↑x, was_visited_if_not_adj x.val x.prop ne_adj ⟩ = (hsearch_step_expand heur priorState stackHead stackTail).mother x := by
      intro x ne_adj_head
      unfold hsearch_step_expand
      grind

    have h_dec_1 :
      ∀ x ∈ priorState.visited, ((hsearch_step_expand heur priorState stackHead stackTail).pathOrder x).1 ≤ (priorState.pathOrder x).1:= by
      intro x
      unfold hsearch_step_expand
      simp_all
      split_ifs <;> simp_all

    have h_dec_2 :
      ∀ x ∈ priorState.visited, ((hsearch_step_expand heur priorState stackHead stackTail).pathOrder x).1 = (priorState.pathOrder x).1 → ((hsearch_step_expand heur priorState stackHead stackTail).pathOrder x).2 ≤ (priorState.pathOrder x).2:= by
      intro x
      unfold hsearch_step_expand
      simp_all
      split_ifs <;> simp_all

    have h_new_visi :
      ∀ x : V, ∀ adj : g.Adj stackHead x, x ∉ priorState.visited → ((hsearch_step_expand heur priorState stackHead stackTail).pathOrder x).1 ≤ (path_val priorState stackHead x adj).1:= by
      intro x
      unfold hsearch_step_expand
      simp_all

    have minvar : ∀ a_visited : a ∈ priorState.visited, (priorState.pathOrder (priorState.mother ⟨a, a_visited⟩)).1 ≤ (priorState.pathOrder a).1 := by
      intro a_visited
      unfold WeightedDiGraph.search_invar_mother_decreasing_path_order at mother_decreasing_prior
      specialize mother_decreasing_prior ⟨a,a_visited⟩ a_not_start
      unfold FValueComp.lt at mother_decreasing_prior
      unfold Nat.instFValueCompProd at mother_decreasing_prior
      simp at mother_decreasing_prior
      grind

    have minvar_2 : ∀ a_visited : a ∈ priorState.visited, (priorState.pathOrder (priorState.mother ⟨a, a_visited⟩)).1 = (priorState.pathOrder a).1 → (priorState.pathOrder (priorState.mother ⟨a, a_visited⟩)).2 < (priorState.pathOrder a).2 := by
      intro a_visited eq_1
      unfold WeightedDiGraph.search_invar_mother_decreasing_path_order at mother_decreasing_prior
      specialize mother_decreasing_prior ⟨a,a_visited⟩ a_not_start
      unfold FValueComp.lt at mother_decreasing_prior
      unfold Nat.instFValueCompProd at mother_decreasing_prior
      simp at mother_decreasing_prior
      grind

    have x_still_visited : ∀ x : priorState.visited, ↑x ∈ (hsearch_step_expand heur priorState stackHead stackTail).visited := by
      intro x
      unfold hsearch_step_expand
      grind

    have mother_same_order : ∀ x : priorState.visited, ∀ adj_head_x : g.Adj stackHead x,
      ((hsearch_step_expand heur priorState stackHead stackTail).mother ⟨x.val, x_still_visited x⟩) = (priorState.mother x) ∧ (priorState.mother x) ≠ stackHead →
      (hsearch_step_expand heur priorState stackHead stackTail).pathOrder x = priorState.pathOrder x := by
        intro x adj_head_x mother_same
        unfold hsearch_step_expand at mother_same ⊢
        grind


    have head_order_stays : ((hsearch_step_expand heur priorState stackHead stackTail).pathOrder stackHead).1 = (priorState.pathOrder stackHead).1 := by
      unfold hsearch_step_expand
      simp
      split_ifs
      · rfl
      · rfl
      · next h_1 h_2 =>
        grind
      · rfl

    by_cases adj_head_a : g.Adj stackHead a
    · clear h_order h_mother
      apply a_a_imp_b_to_a_and_b
      and_intros
      · symm
        apply first_dim.antisymm
        clear first_dim
        by_cases a_visited : a ∈ priorState.visited
        · have mother_options := hsearch_mother_options heur priorState stackHead stackTail ⟨ a, a_visited⟩ (x_still_visited ⟨ a, a_visited⟩)
          cases mother_options
          · next mother_head =>
            rw [mother_head]
            rw [head_order_stays]
            unfold hsearch_step_expand at mother_head ⊢
            simp_all
            grind
          · next mother_same_and_not_head =>
            obtain ⟨ mother_same, mother_not_head ⟩ := mother_same_and_not_head
            rw [mother_same]
            specialize mother_same_order ⟨a,a_visited⟩ adj_head_a ⟨ mother_same, mother_not_head⟩
            rw [mother_same_order]
            unfold hsearch_step_expand at mother_same ⊢
            simp
            split_ifs <;> grind
        · unfold hsearch_step_expand
          simp
          grind
      · by_cases a_visited : a ∈ priorState.visited
        · intro eq
          have mother_options := hsearch_mother_options heur priorState stackHead stackTail ⟨ a, a_visited⟩ (x_still_visited ⟨ a, a_visited⟩)
          cases mother_options
          · next mother_head =>
            rw [mother_head] at ⊢ eq
            unfold hsearch_step_expand at mother_head eq ⊢
            simp_all
            grind
          · next mother_same_and_not_head =>
            obtain ⟨ mother_same, mother_not_head ⟩ := mother_same_and_not_head
            rw [mother_same] at ⊢ eq
            specialize mother_same_order ⟨a,a_visited⟩ adj_head_a ⟨ mother_same, mother_not_head⟩
            rw [mother_same_order] at ⊢ eq
            unfold hsearch_step_expand at mother_same eq ⊢
            simp at ⊢ eq
            split_ifs <;> grind
        · unfold hsearch_step_expand
          simp
          grind
    · have a_visited : a ∈ priorState.visited := was_visited_if_not_adj a a_now_visited adj_head_a
      apply a_a_imp_b_to_a_and_b
      specialize h_order a adj_head_a
      rw [← h_order] at first_dim ⊢
      specialize h_mother ⟨a,a_now_visited⟩ adj_head_a
      rw [← h_mother] at first_dim ⊢
      and_intros
      · symm
        apply first_dim.antisymm
        clear first_dim
        apply le_trans
        · apply h_dec_1
          grind -- from mother visited invariant
        · grind
      · intro first_dim_eq
        clear first_dim
        apply lt_of_le_of_lt
        ·
          let m := priorState.mother ⟨a, a_visited⟩
          have m_visited : m ∈ priorState.visited := by grind
          have h_1 : ((hsearch_step_expand heur priorState stackHead stackTail).pathOrder m).1 = (priorState.pathOrder m).1 := by grind
          specialize h_dec_2 m m_visited h_1
          apply h_dec_2
        · unfold WeightedDiGraph.search_invar_mother_decreasing_path_order at mother_decreasing_prior
          specialize mother_decreasing_prior ⟨a,a_visited⟩ a_not_start
          unfold FValueComp.lt at mother_decreasing_prior
          unfold Nat.instFValueCompProd at mother_decreasing_prior
          grind

lemma hsearch_expand_keeps_on_stack_or_all_neighbours_visited
    (priorState : hsearch_search_state  g)
    (stackHead : V)
    (stackTail : List V):
     WeightedDiGraph.search_invar_on_stack_or_all_neighbours_visited priorState
     ∧ priorState.stack = (stackHead :: stackTail)
     → WeightedDiGraph.search_invar_on_stack_or_all_neighbours_visited
          (hsearch_step_expand heur priorState stackHead stackTail)
          := by
      intro ⟨ invar_holds_on_prior_state, stack_composition ⟩
      unfold WeightedDiGraph.search_invar_on_stack_or_all_neighbours_visited
      intro ⟨ x, x_now_on_stack⟩
      by_cases x_not_stack_head : x ≠ stackHead
      · by_cases x_was_not_in_stack_tail_: x ∈ stackTail
        · left
          unfold hsearch_step_expand
          simp_all
        · by_cases x_not_visited : x ∉ priorState.visited
          · left
            unfold hsearch_step_expand
            unfold hsearch_step_expand at x_now_on_stack
            simp at x_now_on_stack
            simp_all
          · simp_all -- x was visited before and is not on the stack any more
            right
            intro y x_adj_y
            unfold hsearch_step_expand
            simp_all
            left
            have x_invar := invar_holds_on_prior_state x
            simp_all
      · simp_all
        right
        intro y x_adj_y
        unfold hsearch_step_expand
        simp_all
        by_cases h : y ∈ priorState.visited
        · left; exact h
        · right; left; exact h

lemma hsearch_expand_keeps_start_visited
    (start : V)
    (priorState : hsearch_search_state  g)
    (stackHead : V)
    (stackTail : List V):
     WeightedDiGraph.search_invar_start_visited start priorState →
     WeightedDiGraph.search_invar_start_visited start (hsearch_step_expand heur priorState stackHead stackTail)
          := by
      intro pre_invar
      unfold hsearch_step_expand
      unfold WeightedDiGraph.search_invar_start_visited
      simp_all

lemma hsearch_expand_visited_subset (priorState : hsearch_search_state  g)
    (stackHead : V)
    (stackTail : List V):
    priorState.visited ⊆ (hsearch_step_expand heur priorState stackHead stackTail).visited := by
    unfold hsearch_step_expand
    simp_all

lemma hsearch_expand_keeps_goal_on_stack :
   WeightedDiGraph.base_invar_carries_over_expand (state_type := hsearch_search_state g) (hsearch_step_expand heur) goal (WeightedDiGraph.search_prop_goal_on_stack (G:=g) (D:=ℕ × ℕ) goal):= by
    unfold WeightedDiGraph.base_invar_carries_over_expand
    intro s head tail ⟨ goal_prior_on_stack, head_not_goal, compose⟩
    change WeightedDiGraph.search_prop_goal_on_stack goal (hsearch_step_expand heur s head tail)
    unfold hsearch_step_expand
    unfold WeightedDiGraph.search_prop_goal_on_stack at ⊢ goal_prior_on_stack
    simp_all
    cases  goal_prior_on_stack
    all_goals
      simp_all

lemma hsearch_expand_goal_becomes_visited_puts_it_on_stack
  (goal : V)
  :
  WeightedDiGraph.goal_becomes_visited_puts_it_on_stack (state_type := hsearch_search_state g) (G:=g) (D:=ℕ×ℕ) (hsearch_step_expand heur) goal := by
    unfold WeightedDiGraph.goal_becomes_visited_puts_it_on_stack
    intro s head tail ⟨ a,b,c,d⟩
    change WeightedDiGraph.search_prop_goal_on_stack goal (hsearch_step_expand heur s head tail)
    have bb : goal ∈ (hsearch_step_expand heur s head tail).visited := b
    clear b
    unfold hsearch_step_expand at bb ⊢
    unfold WeightedDiGraph.search_prop_goal_on_stack
    simp_all
    cases bb
    · contradiction
    · next h => right; exact h


lemma hsearch_expand_keeps_base_invars:
  WeightedDiGraph.base_invar_carries_over_expand (state_type := hsearch_search_state g) (hsearch_step_expand heur) goal (WeightedDiGraph.search_invar_all_basic (G:=g) (D:=ℕ×ℕ) start) := by
  unfold WeightedDiGraph.base_invar_carries_over_expand
  unfold WeightedDiGraph.search_invar_all_basic
  intro s head tail ⟨ ⟨ i1,i2,i3,i4,i5,i6⟩ , head_not_goal, compose⟩
  have head_is_visited : head ∈ s.visited := by
    apply i1
    rw [compose]
    simp
  and_intros
  · apply hsearch_expand_keeps_stack_in_visited
    constructor
    · exact i1
    · constructor
      · exact head_is_visited
      · intro x x_not_visited
        by_contra x_in_tail
        have x_on_stack : x ∈ (WeightedDiGraph.has_base_search_state.to_base_state (G:=g) (D:=ℕ×ℕ) s).stack := by
          rw [compose]
          simp_all
        apply i1 at x_on_stack
        contradiction
  · apply hsearch_expand_keeps_mother_in_visited
    constructor
    · exact i2
    · exact head_is_visited
  · apply hsearch_expand_keeps_mother_is_adjacent
    exact i3
  · apply hsearch_expand_keeps_mother_ordered
    constructor
    · exact i2
    · constructor
      · exact head_is_visited
      · and_intros
        · exact i4
        · exact i2
  · apply hsearch_expand_keeps_on_stack_or_all_neighbours_visited
    constructor
    · exact i5
    · exact compose
  · apply hsearch_expand_keeps_start_visited
    exact i6


/-- The differene in path order between a node an its mother corresponds to the cost of the edge between them. The mother however might have an even *lower* path order if it has been updated, but that update has not been propagated to the child yet -/
abbrev hsearch_path_order_diff_by_edge_cost (start : V) (s : WeightedDiGraph.base_search_state g (ℕ×ℕ)) :=
    ∀ mother_invar_adj : WeightedDiGraph.search_invar_mother_is_adjacent start s,
    ∀ u : V, (h : u ∈ s.visited) → (ne_start : u ≠ start) →
      (s.pathOrder u).1 ≥ (s.pathOrder (s.mother ⟨u,h⟩)).1 +
        g.edgeCost (mother_invar_adj ⟨u,h⟩ ne_start)




lemma hsearch_path_extracted_not_longer_than_path_order (start : V) (s : WeightedDiGraph.base_search_state g (ℕ×ℕ))
    (mother_invar : search_invar_mother_is_visited  s)
    (mother_invar_adj : search_invar_mother_is_adjacent start s)
    (decreasing_invar : search_invar_mother_decreasing_path_order start s)
    (diff_invar : hsearch_path_order_diff_by_edge_cost start s)
    (u : V)
    (u_visited : u ∈ s.visited):
    (WeightedDiGraph.extract_path_to start u s u_visited mother_invar mother_invar_adj decreasing_invar).1.cost ≤ (s.pathOrder u).1 := by
    by_cases u_ne_start : u ≠ start
    · unfold extract_path_to
      simp
      split
      · rename_i u_eq_start
        contradiction
      · have d := diff_invar mother_invar_adj u u_visited u_ne_start
        apply le_trans
        rotate_left
        · apply d
        · simp_all
          rw [← Path.cost_same]
          rw [Path.concat_inc_cost_by_edge]
          conv =>
            right
            rw [add_comm]
          unfold edgeCost
          apply Nat.add_le_add_left
          apply hsearch_path_extracted_not_longer_than_path_order
          apply diff_invar
    · simp at u_ne_start
      subst u_ne_start
      unfold extract_path_to
      simp_all
termination_by FValueComp.wf.wrap (s.pathOrder u)
decreasing_by
  apply decreasing_invar
  simp_all

section
variable (state : WeightedDiGraph.base_search_state g (ℕ×ℕ))


lemma hsearch_expand_keeps_on_path_order_diff(start goal : V)
    (stack_visited_invar : WeightedDiGraph.search_invar_stack_is_visited state)
    (mother_invar_adj : search_invar_mother_is_adjacent start state)
    (mother_invar : search_invar_mother_is_visited state)
    :
     ∀ head : V, ∀ tail : List V,
        hsearch_path_order_diff_by_edge_cost start state
          ∧ head ≠ goal
          ∧ state.stack = head :: tail
        → hsearch_path_order_diff_by_edge_cost start (hsearch_step_expand heur state head tail) := by
  intro head tail ⟨prior_diff,head_ne_goal,compose⟩
  unfold hsearch_path_order_diff_by_edge_cost
  intro now_mother_adj_invar u u_now_visited head_ne_start
  by_cases u_visited : u ∈ state.visited
  ·
    have mother_options := hsearch_mother_options heur state head tail ⟨u,u_visited⟩ u_now_visited
    cases mother_options
    case pos.inl mother_head =>
      simp at mother_head
      conv =>
        right
        arg 1
        rw [mother_head]
      unfold hsearch_step_expand at ⊢ mother_head
      unfold hsearch_path_order_diff_by_edge_cost at prior_diff
      specialize prior_diff mother_invar_adj u

      by_cases adj_head_u : g.Adj head u <;> by_cases adj_head_head : g.Adj head head <;> (simp_all ; try grind)
    case pos.inr ne_mother =>
      obtain ⟨mother_same,mother_ne_head⟩ := ne_mother
      simp at mother_same
      conv =>
        right
        arg 1
        rw [mother_same]
      unfold hsearch_path_order_diff_by_edge_cost at prior_diff
      specialize prior_diff mother_invar_adj u
      unfold search_invar_mother_is_visited at mother_invar
      specialize mother_invar ⟨u,u_visited⟩
      unfold hsearch_step_expand
      unfold hsearch_step_expand at mother_same
      by_cases adj_head_u : g.Adj head u <;> by_cases adj_head_mother : g.Adj head (state.mother ⟨u, u_visited⟩) <;> (simp_all ; try grind)
  · have adj_head_u : g.Adj head u := by
      unfold hsearch_step_expand at u_now_visited
      simp_all
    unfold hsearch_step_expand
    simp_all
    by_cases adj_head_head : g.Adj head head
    · simp_all
      split <;> simp_all
    · simp_all


abbrev hsearch_invar_on_stack_or_all_neighbours_max_order (s : WeightedDiGraph.base_search_state g (ℕ×ℕ)):=
  ∀ x : s.visited, ↑x ∉ s.stack → ∀ y : V, (adj : g.Adj x y) → (s.pathOrder y).1 ≤ (s.pathOrder x).1 + g.edgeCost adj


lemma hsearch_expand_keeps_on_stack_or_nei_max_order(goal : V)
    (on_stack_or_nei_visited : WeightedDiGraph.search_invar_on_stack_or_all_neighbours_visited state)
    :
     ∀ head : V, ∀ tail : List V,
        hsearch_invar_on_stack_or_all_neighbours_max_order  state
          ∧ head ≠ goal
          ∧ state.stack = head :: tail
        → hsearch_invar_on_stack_or_all_neighbours_max_order  (hsearch_step_expand heur state head tail) := by
      unfold hsearch_invar_on_stack_or_all_neighbours_max_order
      simp
      intro head tail prior_invar head_ne_goal compose a a_visited_after a_not_on_stack_after y a_adj_y

      unfold hsearch_step_expand at a_visited_after a_not_on_stack_after
      simp at a_visited_after a_not_on_stack_after
      obtain ⟨ a_not_in_tail, a_visi_if_head_adj ⟩ := a_not_on_stack_after
      cases a_visited_after
      · next a_visited_before =>
        by_cases a_eq_head : a = head
        · subst a_eq_head
          by_cases y_visited_before : y ∈ state.visited
          · unfold hsearch_step_expand
            simp [y_visited_before, a_visited_before]
            split_ifs <;> grind
          · unfold hsearch_step_expand
            simp [y_visited_before, a_visited_before]
            grind
        · by_cases y_visited_before : y ∈ state.visited
          · unfold hsearch_step_expand
            simp [y_visited_before, a_visited_before]
            split_ifs <;> grind
          · unfold hsearch_step_expand
            simp [y_visited_before, a_visited_before]
            split <;> (simp_all ; grind)
      · next both =>
        obtain ⟨ head_adj_a, a_ne_visited ⟩ := both
        grind -- contradictory



@[simp]
abbrev hsearch_invar_start_path_order_zero_zero (start : V) (s : WeightedDiGraph.base_search_state g (ℕ×ℕ)) :=
      s.pathOrder start = (0,0)


lemma hsearch_expand_start_path_order_zero_carries (start : V) (goal : V)
    (start_visited : WeightedDiGraph.search_invar_start_visited start state)
    :
     ∀ head : V, ∀ tail : List V,
        hsearch_invar_start_path_order_zero_zero start state
          ∧ ¬ head = goal
          ∧ state.stack = head :: tail
        → hsearch_invar_start_path_order_zero_zero start (hsearch_step_expand heur state head tail) := by
      intro head tail ⟨ prior_invar,head_ne_goal,compose⟩
      unfold hsearch_invar_start_path_order_zero_zero
      unfold hsearch_step_expand
      simp_all


end

end NatGraph
