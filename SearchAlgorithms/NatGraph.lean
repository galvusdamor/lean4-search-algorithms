import Graphlib.Basic
import Graphlib.FinEnum


def NatGraph (V : Type) [FinEnum V] : Type := WeightedDiGraph V ℕ

namespace NatGraph
variable {V : Type} [FinEnum V]
variable {G : NatGraph V}


def edgeCost {u v : V} (h : G.Adj u v) : ℕ := G.Payload u v h

end NatGraph


namespace WeightedDiGraph

variable {V : Type} [FinEnum V]
variable {G : NatGraph V}

namespace Walk

/-- `Cost` of a walk is sum of the number of all of its edges-/
def cost {u v : V} : (G.Walk u v) → ℕ
  | WeightedDiGraph.Walk.cons adj rest => (G.edgeCost adj) + cost rest
  | WeightedDiGraph.Walk.nil => 0


@[simp]
theorem append_cons_inc_cost_by_edge (w : G.Walk u v) (h : G.Adj v v') :
  (w.append (Walk.cons h Walk.nil)).cost = G.edgeCost h + w.cost := by
  unfold Walk.append
  split
  · repeat unfold Walk.cost
    simp_all
  · unfold Walk.cost
    conv =>
      right
      rw [add_comm]
      rw [add_assoc]
      right
      rw [add_comm]
    apply Nat.add_left_cancel_iff.mpr
    apply append_cons_inc_cost_by_edge

@[simp]
theorem append_cost (w : G.Walk u v) (w' : G.Walk v v') :
  (w.append w').cost = w.cost + w'.cost := by
  induction w with
  | nil => simp [Walk.append, Walk.cost]
  | cons h p ih =>
    simp [Walk.append, Walk.cost, ih, Nat.add_assoc]

@[simp]
theorem concat_inc_cost_by_edge (p : G.Walk u v) (h : G.Adj v w) :
      (p.concat h).cost = G.edgeCost h + p.cost := by
  unfold Walk.concat
  apply append_cons_inc_cost_by_edge

@[simp]
theorem cost_nil_zero {u : V} : (Walk.nil : G.Walk u u).cost = 0 := by unfold cost ; rfl

theorem contains_subwalk_cost {u v w : V} (p : G.Walk u v) (w_in_walk : w ∈ p.support) (w_ne_v : w ≠ v):
    ∃ p' : G.Walk u w, p'.cost ≤ p.cost ∧ p'.support <+: p.support := by
    by_cases u_eq_w : u = w
    · let w' : G.Walk u u := Walk.nil
      use u_eq_w ▸ w'
      subst u_eq_w
      rw [cost_nil_zero]
      simp_all
      unfold support
      grind
    · cases p
      · unfold support at w_in_walk
        simp_all -- contradictory
      · next a b c =>
        unfold support at w_in_walk
        simp_all
        cases w_in_walk
        · grind
        · next w_in_c =>
          obtain ⟨p',length_le⟩ := contains_subwalk_cost c w_in_c w_ne_v
          use (Walk.cons b p')
          unfold cost
          constructor
          · grind
          · simp_all



@[simp]
theorem dropUntilMakesCheaper (p : G.Walk u v) (f : V) (h : f ∈ p.support):
  (p.dropUntil f h).cost ≤ p.cost := by
  induction p with
  | nil =>
    unfold cost dropUntil
    split
    · next nil_eq_cons =>
      simp at nil_eq_cons
      exfalso
      apply walk_trans (V:=V)
      apply nil_eq_cons
    · simp
  | cons _ p' ih =>
    unfold dropUntil
    split
    · rename_i h_2
      subst h_2
      simp_all only [le_refl]
    · trans
      · apply ih
      · simp!


theorem cost_bypass_le (p : G.Walk u v) : p.bypass.cost ≤ p.cost:= by
  induction p with
  | nil =>
    unfold bypass cost
    rfl
  | cons f_adj_t p' ih =>
    unfold bypass
    simp_all
    split
    · conv =>
        right
        unfold cost
      trans
      · apply dropUntilMakesCheaper
      · grind
    · unfold cost
      grind



end Walk

namespace Path

def cost {u v : V} (p : G.Path u v) : ℕ := Walk.cost p.val

/-- Cast preserves Path cost. -/
lemma path_subst_cost {start a b : V} (e : a = b) (p : G.Path start a) :
    (show G.Path start b from e ▸ p).val.cost = p.val.cost := by
  subst e; rfl

@[simp]
theorem cost_same {u v : V} (p : G.Path u v):
    p.cost = p.val.cost := by unfold cost ; rfl

@[simp]
theorem cost_nil_zero {u : V} : (G.nil_path u).cost = 0 := by
  unfold cost nil_path
  unfold Walk.cost
  simp_all

@[simp]
theorem cost_nil_walk_zero {u : V} : (G.nil_path u).val.length  = 0 := by
  unfold Walk.length nil_path
  simp_all

@[simp]
theorem cost_empty_zero {u : V} (p : G.Path u u) : p.cost = 0 := by
  unfold cost
  unfold Walk.cost
  cases compose : p.val
  · simp
  case cons w h p' =>
    have u_in_p' : u ∈ p'.support := by simp
    have p_prop := p.prop
    unfold List.Nodup at p_prop
    rw [compose] at p_prop
    apply List.pairwise_cons.mp at p_prop
    grind

@[simp]
theorem concat_inc_cost_by_edge (p : G.Path u v) (h : G.Adj v w) (proof_w_not_in_support : w ∉ p.support) :
      (p.concat h proof_w_not_in_support).cost = G.edgeCost h + p.cost := by
  apply Walk.concat_inc_cost_by_edge



def is_cheapest {u v : V} (p : G.Path u v) : Prop :=
  ∀ p' : G.Path u v, p.cost ≤ p'.cost


theorem contains_subpath_cost {u v w : V} (p : G.Path u v) (w_in_path : w ∈ p.support) (w_ne_v : w ≠ v):
    ∃ p' : G.Path u w, p'.cost ≤ p.cost ∧ p'.support <+: p.support := by
    obtain ⟨w',len,supp⟩ := p.val.contains_subwalk_cost w_in_path w_ne_v
    have p_nodup : w'.support.Nodup := by
      apply List.Nodup.sublist (l₂ := p.support)
      · apply List.IsPrefix.sublist
        exact supp
      · exact p.prop
    use ⟨ w', p_nodup⟩
    constructor
    · unfold cost
      apply len
    · unfold Path.support
      apply supp


theorem non_cheapest_path_has_cheaper {u v : V} (p : G.Path u v):
  ¬ is_cheapest p → ∃ p' : G.Path u v, p'.cost < p.cost := by
  unfold is_cheapest
  simp

theorem non_cheapest_path_has_cheaper_cheapest {u v : V} (p : G.Path u v):
  ¬ is_cheapest p → ∃ p' : G.Path u v, is_cheapest p' ∧ p'.cost < p.cost := by
  intro prop
  --unfold is_cheapest
  obtain ⟨p',p'_cheaper⟩ := non_cheapest_path_has_cheaper p prop
  by_cases is_cheapest p'
  case pos cheapest =>
    grind
  case neg not_cheapest =>
    obtain ⟨p'',p''_cheapest, p''_lt⟩ := non_cheapest_path_has_cheaper_cheapest p' not_cheapest
    use p''
    constructor
    · exact p''_cheapest
    · apply lt_trans
      · exact p''_lt
      · exact p'_cheaper
termination_by p.cost



theorem sufficient_cheapest_path_cheaper {u v : V} (p : G.Path u v):
    (∀ p' : G.Path u v, is_cheapest p' → p'.cost ≥ p.cost) →
      is_cheapest p := by
  intro prop
  unfold is_cheapest
  intro p'
  by_cases is_cheapest p'
  case pos cheapest =>
    exact prop p' cheapest
  case neg not_cheapest =>
    obtain ⟨p'', p''_cheapest, p''_cheaper ⟩ := non_cheapest_path_has_cheaper_cheapest p' not_cheapest
    apply le_trans
    · exact prop p'' p''_cheapest
    · apply p''_cheapest p'


end Path

namespace Walk

theorem cheaper_path_exists (w : G.Walk u v):
  ∃ p : G.Path u v, p.cost ≤ w.cost := by
  let w' : G.Walk u v := w.bypass
  have nodup : w'.support.Nodup := by unfold w' ; apply bypass_isPath
  use ⟨ w', nodup ⟩
  unfold Path.cost
  apply cost_bypass_le


end Walk

namespace Path
/-
PROBLEM
A subpath (prefix) of a cheapest path is itself cheapest.

PROVIDED SOLUTION
By contradiction. Suppose q : g.Path u w with ¬(⟨uw, nodup⟩.cost ≤ q.cost), i.e. q.cost < uw.cost. Form walk q.val.append wv. Its cost is q.cost + wv.cost (by Walk.append_cost). Since uw.cost + wv.cost = (uw.append wv).cost = p.val.cost (using compose and Walk.append_cost), we have q.cost + wv.cost < uw.cost + wv.cost = p.val.cost. By Walk.cheaper_path_exists, obtain p' : g.Path u v with p'.cost ≤ (q.val.append wv).cost < p.cost. This contradicts p_cheapest p'.
-/
lemma subpath_of_cheapest_is_cheapest {u v w : V}
    (p : G.Path u v) (uw : G.Walk u w) (wv : G.Walk w v)
    (compose : uw.append wv = p.val)
    (nodup : uw.support.Nodup)
    (p_cheapest : p.is_cheapest) :
    Path.is_cheapest (⟨uw, nodup⟩ : G.Path u w) := by
      intro q
      by_contra hq
      -- Let's construct the walk $q.append wv$ and show that its cost is strictly less than $p$'s cost.
      have h_walk_cost : (q.val.append wv).cost < p.val.cost := by
        simp [cost_same, not_le] at hq
        apply lt_of_lt_of_eq ; rotate_left
        · rw [← compose]
        · repeat rw [Walk.append_cost ]
          apply add_lt_add_left
          exact hq
      -- By `Walk.cheaper_path_exists`, there exists a path `p'` with `p'.cost ≤ (q.val.append wv).cost`.
      obtain ⟨p', hp'⟩ : ∃ p' : G.Path u v, p'.cost ≤ (q.val.append wv).cost := by
        exact Walk.cheaper_path_exists (q.val.append wv)

      exact not_lt_of_ge ( p_cheapest p' ) ( lt_of_le_of_lt hp' h_walk_cost )


end Path

end WeightedDiGraph

namespace NatGraph
variable {V : Type} [FinEnum V]
variable {G : NatGraph V}

def cost_is (u v : V) (dist: ℕ) : Prop :=
  (∃ p : G.Path u v, p.cost = dist ∧ p.is_cheapest)

def cost_ge (u v : V) (dist: ℕ) : Prop :=
  ∀ p : G.Path u v, p.cost ≥ dist

def cost_gt (u v : V) (dist: ℕ) : Prop :=
  ∀ p : G.Path u v, p.cost > dist

def cost_lt (u v : V) (dist: ℕ) : Prop :=
  ∃ p : G.Path u v, p.cost < dist

lemma cost_ge_lt (u v : V) (d1 d2: ℕ) :
    G.cost_ge u v d1 ∧ d2 ≤ d1 → G.cost_ge u v d2 := by
    unfold NatGraph.cost_ge
    simp_all
    intro ge_d1 d2_le_d1 p p_nodup
    apply le_trans
    · exact d2_le_d1
    · exact ge_d1 p p_nodup


lemma cost_v_v (v : V) : G.cost_is v v 0 := by
  unfold cost_is
  use G.nil_path v
  unfold WeightedDiGraph.Path.is_cheapest
  constructor
  · simp_all only [WeightedDiGraph.Path.cost_same]
    rfl
  · intro p'
    simp_all only [WeightedDiGraph.Path.cost_same]
    apply le_trans (b:=0)
    · rfl
    · apply zero_le

end NatGraph

namespace NatGraph

def add_artificial_goal {V : Type} [FinEnum V] (G : NatGraph V) (goals : List V) : NatGraph (Option V) :=
  let nAdj : Option V → Option V → Prop := fun a b =>
    match (a,b) with
     | (none, none) => ⊥
     | (none, some _) => ⊥
     | (some g ,none) => g ∈ goals
     | (some a', some b') => G.Adj a' b'

  let g : Digraph (Option V) := Digraph.mk nAdj

  let nPay : (u v : Option V) -> (g.Adj u v) -> ℕ := fun u v adj =>
    match eq : (u,v) with
     | (none, none) => ⊥
     | (none, some _) => ⊥
     | (some g ,none) => 0 -- cost from actual goal to artificial one is 0
     | (some a', some b') =>
        have adj' : G.Adj a' b' := by
          unfold g nAdj at adj
          simp at adj
          split at adj <;> try contradiction
          · grind -- contradictory some = none
          · convert adj <;> grind
        G.Payload a' b' adj'

  let nDec : DecidableRel g.Adj := by
    unfold DecidableRel
    intro a b
    unfold g nAdj
    simp
    split
    · apply Decidable.isFalse
      simp
    · apply Decidable.isFalse
      simp
    · expose_names; exact List.instDecidableMemOfLawfulBEq g_1 goals
    · expose_names; apply G.instDecAdj a' b'

  WeightedDiGraph.mk g nPay nDec


variable {V : Type} [FinEnum V]
variable {G : NatGraph V}


/-- In the augmented graph, `none` has no outgoing edges. -/
lemma add_artificial_goal_none_not_adj {goals : List V}
    (v : Option V) : ¬ (G.add_artificial_goal goals).Adj none v := by
  unfold NatGraph.add_artificial_goal; simp
  cases v <;> simp


/-
PROBLEM
In the augmented graph, if a walk ends at `some b`, then `none` is not in its support.

PROVIDED SOLUTION
By induction on w.

Base case (nil): walk from a to some b with a = some b, support = [some b], none ∉ [some b] trivially.

Cons case (cons adj rest): walk from a to some b via intermediate vertex mid, with adj : Adj a mid and rest : Walk mid (some b).
  support = a :: rest.support.
  By IH, none ∉ rest.support.
  We need a ≠ none. If a = none, then adj : Adj none mid, but add_artificial_goal_none_not_adj says ¬Adj none mid, contradiction.
  So a ≠ none, hence none ∉ a :: rest.support.
-/
lemma none_not_in_walk_to_some {goals : List V} {a : Option V} {b : V}
    (w : (G.add_artificial_goal goals).Walk a (some b)) :
    Option.none ∉ w.support := by
      -- If none is in the support of w, then it would imply that there's a step where none is adjacent to some other node, which is impossible.
      by_contra h_contra
      obtain ⟨mid, hmid⟩ : ∃ mid, (G.add_artificial_goal goals).Adj none mid := by
        have h_adj : ∀ {u v : Option V} (w : (G.add_artificial_goal goals).Walk u v), none ∈ w.support → ∃ mid, (G.add_artificial_goal goals).Adj none mid := by
          intros u v w hw; induction w <;> simp_all +decide [ NatGraph.add_artificial_goal_none_not_adj ] ; (
          have h_support : ∀ {u v : Option V} (w : (G.add_artificial_goal goals).Walk u v), u = none → v = none := by
            intros u v w hu;  induction w
            · subst hu
              simp_all only
            · rename_i h p p_ih
              subst hu
              apply p_ih
              ext a_1 : 1
              simp_all only [reduceCtorEq, iff_false]
              by_contra a_2
              subst a_2
              simp_all only [reduceCtorEq, IsEmpty.forall_iff]
              exact h
          exact absurd ( h_support ( show ( G.add_artificial_goal goals ).Walk none ( some b ) from by
                                      exact w.dropUntil none h_contra ) rfl ) ( by simp +decide ));
          exact ⟨ _, by subst hw; assumption ⟩
        exact h_adj w h_contra
      cases mid <;> simp_all +decide [ NatGraph.add_artificial_goal ]


/-
PROVIDED SOLUTION
After substituting w_eq_some_w', the path goes from (some start) to (some w'). Apply none_not_in_walk_to_some to path.val (the underlying walk) after the substitution. The key is that w_eq_some_w' ▸ path is a path from (some start) to (some w'), so its underlying walk goes to some w', and by none_not_in_walk_to_some, none is not in its support.
-/
/-- Lift a walk from the original graph to the augmented graph. -/
def lift_walk_to_augmented {goals : List V} {b : V}
    : {a : V} → (w : G.Walk a b) → (G.add_artificial_goal goals).Walk (some a) (some b)
  | _, .nil => WeightedDiGraph.Walk.nil
  | a, .cons (w := mid) adj rest =>
    have adj' : (G.add_artificial_goal goals).Adj (some a) (some mid) := by
      unfold NatGraph.add_artificial_goal; simp; exact adj
    WeightedDiGraph.Walk.cons adj' (lift_walk_to_augmented rest)

/-
PROVIDED SOLUTION
By induction on w, following the same pattern as translate_walk_support_map.

Base (nil): support of nil is [a], map some [a] = [some a] = support of lifted nil.
Cons: support = a :: rest.support, lifted support = some a :: (lift rest).support. By IH, (lift rest).support = map some rest.support. So map some (a :: rest.support) = some a :: map some rest.support = lifted support.
-/
lemma lift_walk_support_eq {goals : List V} {a b : V}
    (w : G.Walk a b) :
    (lift_walk_to_augmented (G:=G) (goals:=goals) w).support = w.support.map some := by
      induction w
      · rfl
      · unfold lift_walk_to_augmented
        simp_all only [WeightedDiGraph.Walk.support_cons, List.map_cons]
/-
PROVIDED SOLUTION
By `lift_walk_support_eq`, we have `(lift_walk_to_augmented w).support = w.support.map some`. Since `w.support.Nodup` (by hypothesis `h`) and `some` is injective (Option.some_injective), we get that `(lift_walk_to_augmented w).support.Nodup` via `List.Nodup.map`.
-/
lemma lift_walk_nodup {goals : List V} {a b : V}
    (w : G.Walk a b) (h : w.support.Nodup) :
    (lift_walk_to_augmented (G:=G) (goals:=goals) w).support.Nodup := by
      convert List.Nodup.map ( Option.some_injective _ ) h using 1
      exact lift_walk_support_eq w

/-
PROBLEM
If a path exists from start to a goal in g, then a path exists
    from (some start) to none in the augmented graph.

PROVIDED SOLUTION
Given p : g.Path start goal, lift it to the augmented graph using lift_walk_to_augmented to get a walk from (some start) to (some goal). This walk has nodup support by lift_walk_nodup. Since goal ∈ goals, we have (g.add_artificial_goal goals).Adj (some goal) none (by definition of add_artificial_goal, since goal ∈ goals). So we can concat this adjacency to get a walk from (some start) to none. We need to show the resulting walk has nodup support. The lifted walk's support doesn't contain none (by none_not_in_walk_to_some or by lift_walk_support_eq showing it's map some of something), and the concat adds none at the end, so it's still nodup. Package this as a Path.
-/
lemma path_in_augmented_exists {goals : List V} {start goal : V}
    (goal_in_goals : goal ∈ goals)
    (p : G.Path start goal) :
    ∃ q : (G.add_artificial_goal goals).Path (some start) none, q = q := by
      simp +zetaDelta at *;
      by_contra h_contra;
      push_neg at h_contra;
      -- By definition of `lift_walk_to_augmented`, we can construct a walk from `some start` to `none` by appending the edge from `some goal` to `none`.
      obtain ⟨w, hw⟩ : ∃ w : (G.add_artificial_goal goals).Walk (some start) (some goal), w.support.Nodup := by
        exact ⟨ NatGraph.lift_walk_to_augmented p.val, NatGraph.lift_walk_nodup p.val p.prop ⟩;

      have h_append : ∃ w' : (G.add_artificial_goal goals).Walk (some start) none, w'.support = w.support ++ [none] := by
        exact ⟨ w.concat ( show ( G.add_artificial_goal goals ).Adj ( some goal ) none from by unfold NatGraph.add_artificial_goal; simp_all only ), by simp ⟩

      obtain ⟨ w', hw' ⟩ := h_append
      specialize h_contra w'
      simp_all +decide [ List.nodup_append ]
      exact absurd h_contra ( by simpa using none_not_in_walk_to_some w )


/-- Translate a walk in the augmented graph to a walk in the original graph,
    assuming `none` does not appear in the walk's support. -/
def translate_walk {b : V} {goals : List V}
    : {a : V} → (w : (G.add_artificial_goal goals).Walk (some a) (some b)) →
    (none_not_in : Option.none ∉ w.support) → G.Walk a b
  | _, .nil, _ => WeightedDiGraph.Walk.nil
  | a, .cons (w := some mid') adj rest, none_not_in => by
    have adj' : G.Adj a mid' := by
      unfold NatGraph.add_artificial_goal at adj
      simpa using adj
    have none_not_in_rest : Option.none ∉ rest.support := by
      intro h; apply none_not_in
      unfold WeightedDiGraph.Walk.support; simp [h]
    exact WeightedDiGraph.Walk.cons adj' (translate_walk rest none_not_in_rest)
  | a, .cons (w := none) adj _, none_not_in => by
    exfalso; apply none_not_in
    unfold WeightedDiGraph.Walk.support; simp

lemma translate_walk_support_map  {b : V} {goals : List V}
    : ∀ {a : V} (w : (G.add_artificial_goal goals).Walk (some a) (some b))
    (none_not_in : Option.none ∉ w.support),
    (G.translate_walk w none_not_in).support.map (fun x => (some x : Option V)) = w.support
  | _, .nil, _ => by simp [translate_walk, WeightedDiGraph.Walk.support]
  | a, .cons (w := some mid') adj rest, none_not_in => by
    unfold translate_walk
    simp only []
    unfold WeightedDiGraph.Walk.support
    simp only [List.map_cons, List.cons.injEq]
    constructor
    · trivial
    · exact translate_walk_support_map rest _
  | a, .cons (w := none) adj _, none_not_in => by
    exfalso; apply none_not_in; unfold WeightedDiGraph.Walk.support; simp

/-
PROVIDED SOLUTION
We know that List.map (fun x => some x) (translate_walk w none_not_in).support = w.support from translate_walk_support_map. Since w.support is nodup (w_nodup), and the map `fun x => some x` is injective (Option.some_injective), we get that (translate_walk w none_not_in).support is also nodup. Use List.Nodup.of_map or the injective map nodup lemma.
-/
lemma translate_walk_nodup {a b : V} {goals : List V}
    (w : (G.add_artificial_goal goals).Walk (some a) (some b))
    (w_nodup : w.support.Nodup)
    (none_not_in : Option.none ∉ w.support) :
    (G.translate_walk w none_not_in).support.Nodup := by
      -- Apply the injectivity of the map and the nodup property of the original support to conclude that the translated support is also nodup.
      have h_nodup_trans : List.Nodup (List.map (fun x => some x) (G.translate_walk w none_not_in).support) := by
        rw [ translate_walk_support_map ] ; assumption;
      exact List.Nodup.of_map (fun x => some x) h_nodup_trans

/-- Translate a path in the augmented graph (with no `none` in support)
    to a path in the original graph. -/
def translate_path {a b : V} {goals : List V}
    (p : (G.add_artificial_goal goals).Path (some a) (some b))
    (none_not_in_p : Option.none ∉ p.support) : G.Path a b :=
  ⟨G.translate_walk p.val none_not_in_p, G.translate_walk_nodup p.val p.prop none_not_in_p⟩


/-- The cost of translating a walk back to the original graph is the same. -/
lemma translate_walk_cost_eq {goals : List V} {b : V} :
    ∀ {a : V} (w : (G.add_artificial_goal goals).Walk (some a) (some b))
    (none_not_in : Option.none ∉ w.support),
    (NatGraph.translate_walk (G:=G) w none_not_in).cost = w.cost
  | _, .nil, _ => by simp [NatGraph.translate_walk, WeightedDiGraph.Walk.cost]
  | a, .cons (w := some mid') adj rest, none_not_in => by
    simp only [NatGraph.translate_walk, WeightedDiGraph.Walk.cost, NatGraph.edgeCost, NatGraph.add_artificial_goal]
    simp only [Nat.add_left_cancel_iff]
    exact translate_walk_cost_eq rest _
  | a, .cons (w := none) adj _, none_not_in => by
    exfalso; apply none_not_in; simp [WeightedDiGraph.Walk.support]

/-
PROBLEM
The cost of lifting a walk to the augmented graph is the same.

PROVIDED SOLUTION
By induction on w. Base case (nil): both costs are 0. Cons case (cons adj rest): w goes from a via mid to b. The lifted walk is cons adj' (lift rest). Cost of lifted = edgeCost adj' + cost(lift rest). By IH, cost(lift rest) = cost rest. We need edgeCost adj' = edgeCost adj. By definition of add_artificial_goal, the payload of (some a, some mid) is G.Payload a mid = edgeCost adj. So the costs match.
-/
lemma lift_walk_cost_eq {goals : List V} {a b : V}
    (w : G.Walk a b) :
    (lift_walk_to_augmented (G:=G) (goals:=goals) w).cost = w.cost := by
  induction w with
  | nil => rfl
  | cons adj rest ih =>
    simp only [lift_walk_to_augmented, WeightedDiGraph.Walk.cost, NatGraph.edgeCost, NatGraph.add_artificial_goal]
    exact congrArg _ ih



/-
PROBLEM
For any path from start to a goal in g, there's an augmented path of equal cost.

PROVIDED SOLUTION
Given p : g.Path start thegoal with thegoal ∈ goals:
1. Lift p.val using lift_walk_to_augmented to get a walk from (some start) to (some thegoal) in the augmented graph.
2. By lift_walk_nodup, this walk has nodup support, so it's a path.
3. Since thegoal ∈ goals, (g.add_artificial_goal goals).Adj (some thegoal) none (by definition of add_artificial_goal).
4. Concat this adjacency to get a walk from (some start) to none.
5. none is not in the lifted walk's support (by lift_walk_support_eq, the support is map some of something, so none can't be in it).
6. So the concatenated walk has nodup support (lifted support ++ [none], with none fresh).
7. Package as a path q.
8. q.cost = lifted_walk.cost + 0 = p.cost + 0 = p.cost (by lift_walk_cost_eq and the 0-cost edge).
-/
lemma lift_path_to_augmented_cost {goals : List V} {start thegoal : V}
    (thegoal_in : thegoal ∈ goals)
    (p : G.Path start thegoal) :
    ∃ q : (G.add_artificial_goal goals).Path (some start) none, q.cost = p.cost := by
      have h_lift : ∃ q : (G.add_artificial_goal goals).Walk (some start) (some thegoal), q.support.Nodup ∧ q.cost = p.cost := by
        use NatGraph.lift_walk_to_augmented (G := G) (goals := goals) p.val;
        exact ⟨ NatGraph.lift_walk_nodup _ p.2, NatGraph.lift_walk_cost_eq _ ⟩;
      obtain ⟨ q, hq₁, hq₂ ⟩ := h_lift;
      obtain ⟨q', hq'⟩ : ∃ q' : (G.add_artificial_goal goals).Walk (some start) none, q'.support.Nodup ∧ q'.cost = q.cost := by
        refine' ⟨ _, _, _ ⟩;
        exact q.concat thegoal_in;
        · simp_all +decide [ List.nodup_append ];
          intro a ha H
          have := hq₁; simp_all +decide [ List.nodup_iff_count_le_one ] ;
          exact absurd ha ( none_not_in_walk_to_some q );
        · simp +decide [ WeightedDiGraph.Walk.concat ];
          rfl;
      exact ⟨ ⟨ q', hq'.1 ⟩, hq'.2.trans hq₂ ⟩

/-- If w is adjacent to none in the augmented graph, then w = some w' for some w' ∈ goals. -/
lemma adj_to_none_is_goal {goals : List V} {w : Option V}
    (h : (G.add_artificial_goal goals).Adj w none) : ∃ w' : V, w = some w' ∧ w' ∈ goals := by
  unfold NatGraph.add_artificial_goal at h
  simp at h
  cases w with
  | none => simp at h
  | some w' => exact ⟨w', rfl, h⟩



end NatGraph
