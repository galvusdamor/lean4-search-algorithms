import Mathlib.Data.Bool.AllAny
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Combinatorics.Digraph.Basic
import Mathlib.Data.Bool.AllAny
import Mathlib.Data.FinEnum
import Init.Data.List.Basic

import Graphlib.Lists

/-!
# Weighted Digraphs

This module defines directed graphs on a vertex type `V` and edge type `E`,
which is the same notion as a relation `payload : (u : V) -> (v : V) -> (Adj u v) -> E`.
This approach extends the Digraph structure, using `Adj u v` from Digraph as a proof
for the adjacency relation.

Note that a weighted digraph may have self loops.

Every edge present in the graph, i.e. where `Adj u v` is returning the decidable Prop `true`,
is associated with an edge label (weight).
This label can be used for various puroses that include, for example, multiedge weights via
`List W` for some type `W`, finite set type, or `Nat`, but also for labeling with propositions
and formulae.
-/


/-- A weighted digraph is a relation `Payload` on a vertex type `V`, a `Prop` and the last
coordinate of label type `E`. Note that a tuple only exists if the decidable `Adj u v` returns
true.
The relation `Adj u v` describes which pairs of vertices are adjacent and is inherited from Digraph.
Since this definition of digraphs is aimed to study algorithms, we force this relation to be #
decidable with `instDecAdj : DecidableRel Adj`.
-/
structure WeightedDiGraph (V : Type) (E : Type) [FinEnum V] extends Digraph V where
  Payload : (u : V) -> (v : V) -> (Adj u v) -> E
  instDecAdj : DecidableRel Adj

-- def local global variable for a graph
variable {V : Type} {E : Type} [FinEnum V] --[DecidableEq V] [DecidableEq E]
variable {G : WeightedDiGraph V E}

namespace WeightedDiGraph

def nodeNum (_ : WeightedDiGraph V E) : ℕ := Fintype.card V

theorem payloadProofIrrelevant (u v : V) (h h' : G.Adj u v) :
    G.Payload u v h = G.Payload u v h' := by dsimp

/-- A `walk` is a sequence of adjacent vertices.  For vertices `u v : V`,
the type `walk u v` consists of all walks starting at `u` and ending at `v`. -/
inductive Walk : V → V → Type
  | nil {u : V} : Walk u u
  | cons {f w t : V} (h : (G.Adj f w)) (p : Walk w t) : Walk f t
  deriving DecidableEq
-- h is hypothese for valid edge, f from node, w next node of starting walk, t to node, p rest node from w to t

attribute [refl] Walk.nil

namespace Walk

/-- Change the endpoints of a walk using equalities. This is helpful for relaxing
definitional equality constraints and to be able to state otherwise difficult-to-state
lemmas. While this is a simple wrapper around `Eq.rec`, it gives a canonical way to write it.

The simp-normal form is for the `copy` to be pushed outward. That way calculations can
occur within the "copy context." -/
protected def copy {u v u' v'} (p : G.Walk u v) (hu : u = u') (hv : v = v') : G.Walk u' v' :=
  hu ▸ hv ▸ p

@[simp]
theorem copy_rfl_rfl {u v} (p : G.Walk u v) : p.copy rfl rfl = p := rfl

@[simp]
theorem copy_copy {u v u' v' u'' v''} (p : G.Walk u v)
    (hu : u = u') (hv : v = v') (hu' : u' = u'') (hv' : v' = v'') :
    (p.copy hu hv).copy hu' hv' = p.copy (hu.trans hu') (hv.trans hv') := by
  subst_vars
  rfl

@[simp]
theorem copy_nil {u u'} (hu : u = u') : (Walk.nil : G.Walk u u).copy hu hu = nil := by
  subst_vars
  rfl

theorem copy_cons {u v w u' w'} (h : G.Adj u v) (p : G.Walk v w) (hu : u = u') (hw : w = w') :
    (Walk.cons h p).copy hu hw = Walk.cons (hu ▸ h) (p.copy rfl hw) := by
  subst_vars
  rfl

@[simp]
theorem cons_copy {u v w v' w'} (h : G.Adj u v) (p : G.Walk v' w') (hv : v' = v) (hw : w' = w) :
    cons h (p.copy hv hw) = (Walk.cons (hv ▸ h) p).copy rfl hw := by
  subst_vars
  rfl

theorem nil_walk_eq {u v: V} (h : u = v): (Walk.nil : G.Walk u u) = h ▸ (Walk.nil : G.Walk v v) := by
  subst h
  simp_all only

/-- `Support` of a walk is the list of edges it visits in order. -/
def support {u v : V} : (G.Walk u v) → List V
  | @Walk.cons _ _ _ _ u _ _ _ rest => u :: support rest
  | Walk.nil => [v]

/-- `Length` of a walk is the number of edges in it-/
def length {u v : V} : (G.Walk u v) → ℕ
  | @Walk.cons _ _ _ _ _ _ _ _ rest => 1 + length rest
  | Walk.nil => 0

@[simp]
theorem length_nil_zero {u : V} : (Walk.nil : G.Walk u u).length = 0 := by unfold length ; rfl

@[simp]
theorem length_diff_ends_ne_zero {u v : V} (h : u ≠ v) (p : G.Walk u v):
  p.length > 0 := by
  unfold length
  split
  · simp
  · contradiction

theorem walk_support_length
    {u v : V} (w : G.Walk u v) : w.support.length = w.length + 1 := by
  induction w with
  | nil => simp [WeightedDiGraph.Walk.support, WeightedDiGraph.Walk.length]
  | cons _ _ ih => simp [support, ih, Nat.add_comm, length]

@[simp]
theorem goal_in_support {u v : V} (p: G.Walk u v): v ∈ p.support := by
  unfold support
  split
  · simp
    right
    apply goal_in_support
  · simp

@[simp]
theorem start_in_support {u v : V} (p: G.Walk u v): u ∈ p.support := by
  unfold support
  split <;> simp

@[simp]
theorem support_ne_nil {u v : V} (p : G.Walk u v): p.support ≠ [] := by
  unfold support
  cases p <;> simp_all

@[simp]
theorem cons_support {x u v w: V} (p: G.Walk v w) (h : G.Adj u v ) :
    x ∈ (Walk.cons h p).support → x = u ∨ x ∈ p.support:= by
  intro x_in_cons_supp
  unfold support at x_in_cons_supp
  grind

@[simp]
theorem support_cons {u v w: V} (p: G.Walk v w) (h : G.Adj u v) :
    (Walk.cons h p).support = u :: p.support:= by
  conv =>
   left
   unfold support

theorem support_last {u v : V} (p : G.Walk u v):
    p.support = p.support.dropLast ++ [v] := by
    induction p
    case nil =>
      unfold support
      simp_all
    case cons h p' ih =>
      unfold support
      conv =>
        right
        unfold List.dropLast
      simp
      apply ih

@[simp]
theorem nodup_and_start_eq_end_support {u v: V} (w : G.Walk u v) (u_eq_v : u = v)
    (nodup : w.support.Nodup) : w.support = [u] := by
  cases w
  · unfold support
    rfl
  · next a b c =>
    unfold support at nodup
    simp at nodup
    have u_not_in_supp := nodup.left
    have h : v ∈ c.support := by apply goal_in_support
    rw [u_eq_v] at u_not_in_supp
    contradiction

@[simp]
theorem nil_support {u : V} (w : G.Walk u u) (nodup : w.support.Nodup) : w.support = [u] := by
  apply nodup_and_start_eq_end_support
  · rfl
  · exact nodup

theorem nil_support_nodup {u : V} : (nil : G.Walk u u).support.Nodup := by
  unfold support
  simp

/-! ## Operations that modify paths and walks -/

/-- Take two walks `w1 : Walk G u v` and `w2 : Walk G v w` and return the
appended walk `Walk G u w` -/
@[trans]
def append {u v w : V} : G.Walk u v → G.Walk v w → G.Walk u w
  | nil, q => q
  | cons h p, q => cons h (p.append q)

/-- The reversed version of `SimpleGraph.Walk.cons`, concatenating an edge to
the end of a walk. -/
def concat {u v w : V} (p : G.Walk u v) (h : G.Adj v w) : G.Walk u w := p.append (cons h nil)

def is_sub_walk_head {u v w : V} (p : G.Walk u v) (p' : G.Walk w v) : Bool :=
  if u = w then true
  else match p with
  | nil => false
  | cons _ p_sub => p_sub.is_sub_walk_head  p'

def is_prefix {u v w : V} (p : G.Walk u v) (p' : G.Walk u w) : Bool :=
  match p' with
  | nil => true -- p' is the empty path already.
  | cons (w:= p'_u') _ p_sub' =>
    match p with
    | Walk.nil => false -- p' is longer than p
    | Walk.cons (w := p_u') _ p_sub =>
      if h : p_u' = p'_u' then is_prefix p_sub (h ▸ p_sub')
      else false

@[simp]
theorem support_concat_is_append_at_end {h : G.Adj v v'} { w : G.Walk u v } :
    (w.concat h).support = w.support ++ [v']  := by
  induction w <;> simp_all [concat, append, support]

@[simp]
theorem append_cons_inc_length_by_one (w : G.Walk u v) (h : G.Adj v v') :
    (w.append (Walk.cons h Walk.nil)).length = 1 + w.length := by
  unfold append
  split
  · simp [length]
  · apply Nat.add_left_cancel_iff.mpr
    apply append_cons_inc_length_by_one

@[simp]
theorem concat_inc_length_by_one (p : G.Walk u v) (h : G.Adj v w) :
    (p.concat h).length = 1 + p.length :=
  append_cons_inc_length_by_one _ _

theorem split_at_end_length_one (p : G.Walk u v) (len_ne_zero : p.length > 0):
    ∃ w : V, ∃ p' : G.Walk u w, ∃ w_adj_v : G.Adj w v,
      p = p'.concat w_adj_v := by
  cases p
  · simp_all [length]
  · next u' u_adj_u' p_u' =>
    cases p_u'
    · use u
      use (Walk.nil : G.Walk u u)
      use u_adj_u'
      unfold concat
      unfold append
      rfl
    · next u'' u'_adj_u'' p_u'' =>
      let p_u' := Walk.cons u'_adj_u'' p_u''
      have p_u'_length : p_u'.length > 0 := by simp [length, p_u']
      obtain ⟨ w,p',w_adj_v, extend_prop⟩ := split_at_end_length_one p_u' p_u'_length
      use w
      use Walk.cons u_adj_u' p'
      use w_adj_v
      unfold concat append
      unfold p_u' at extend_prop
      rw [extend_prop]
      congr

def snoc' (p : G.Walk u v)  (len_ne_zero : p.length > 0):
    Σ w : V, { _p : G.Walk u w // G.Adj w v }:= by
  cases p
  · simp_all [length]
  · next u' u_adj_u' p_u' =>
    cases eq : p_u'
    case nil =>
      use u
      use (Walk.nil : G.Walk u u)
    case cons u'' u'_adj_u'' p_u'' =>
      let p_u' := Walk.cons u'_adj_u'' p_u''
      have p_u'_length : p_u'.length > 0 := by simp [length, p_u']
      obtain ⟨w,pp⟩ := p_u'.snoc' p_u'_length
      have p' : G.Walk u w := Walk.cons u_adj_u' pp
      exact ⟨w,⟨ p',pp.prop⟩⟩

def snoc (p : G.Walk u v) (not_nil : u ≠ v):
    Σ w : V, { _p : G.Walk u w // G.Adj w v }:= by
    have len_ne_zero : p.length > 0 := by
      cases p
      · contradiction
      · simp [length]

    exact snoc' p len_ne_zero

/-- Like `snoc'` but also returns a proof that the walk equals the prefix concatenated with the last edge. -/
def snoc_with_proof (p : G.Walk u v) (h : p.length > 0) :
    Σ w : V, (q : G.Walk u w) × { adj : G.Adj w v // p = q.concat adj } := by
  cases p with
  | nil => simp [length] at h
  | cons u_adj_u' p_u' =>
    cases hp : p_u' with
    | nil =>
      exact ⟨_, Walk.nil, ⟨u_adj_u', by simp [concat, append]⟩⟩
    | cons u'_adj_u'' p_u'' =>
      let p_u'_new : G.Walk _ v := Walk.cons u'_adj_u'' p_u''
      have p_u'_length : p_u'_new.length > 0 := by simp [length, p_u'_new]
      let ⟨w, q, ⟨adj, hq⟩⟩ := snoc_with_proof p_u'_new p_u'_length
      refine ⟨w, Walk.cons u_adj_u' q, ⟨adj, ?_⟩⟩
      change Walk.cons u_adj_u' p_u'_new = (Walk.cons u_adj_u' q).concat adj
      change p_u'_new = q.concat adj at hq
      rw [hq]; simp [concat, append]
theorem split_at_end (p : G.Walk u v) (not_nil : u ≠ v):
    ∃ w : V, ∃ p' : G.Walk u w, ∃ w_adj_v : G.Adj w v,
      p = p'.concat w_adj_v := by
    have len_ne_zero : p.length > 0 := by
      cases p
      · contradiction
      · simp [length]
    apply p.split_at_end_length_one len_ne_zero

def support_of_append {u v w : V} (uv : G.Walk u v) (vw : G.Walk v w):
    (uv.append vw).support = uv.support ++ vw.support.tail := by
  induction uv with
  | nil =>
    cases vw with
    | nil => simp [append, support]
    | cons h p =>
      simp [append, support]
  | cons h p ih =>
    simp [append, support, ih]


/-- If `v'' ∈ uw.support` and `uw.append wv = full`, then `v'' ∈ full.support`. -/
lemma mem_support_prefix_of_append {u v w : V}
    (uw : G.Walk u w) (wv : G.Walk w v) {full : G.Walk u v}
    (compose : uw.append wv = full)
    (v'' : V) (hv : v'' ∈ uw.support) :
    v'' ∈ full.support := by
      -- Rewrite `full.support` using `Walk.support_of_append` and `compose`, then apply `List.mem_append_left` to `hv`.
      simp only [← compose, Walk.support_of_append]
      apply List.mem_append_left
      exact hv


/-
PROBLEM
The prefix of a walk whose full concatenation has `Nodup` support also has `Nodup` support.

PROVIDED SOLUTION
Rewrite the nodup hypothesis using Walk.support_of_append to get uw.support ++ wv.support.tail is Nodup. Then extract nodup of the left part using List.Nodup.of_append_left or similar.
-/
lemma nodup_prefix_of_append_nodup {u v w : V}
    (uw : G.Walk u w) (wv : G.Walk w v)
    (h : (uw.append wv).support.Nodup) : uw.support.Nodup := by
      -- Rewrite the nodup hypothesis using `Walk.support_of_append` to get `uw.support ++ wv.support.tail` is nodup. Then extract nodup of the left part using `List.Nodup.of_append_left`.
      rw [Walk.support_of_append] at h
      apply List.Nodup.of_append_left
      exact h

/-
PROBLEM
The suffix of a walk whose full concatenation has `Nodup` support also has `Nodup` support.

PROVIDED SOLUTION
By induction on uw. Base case (nil): uw.append wv = wv so h is directly wv.support.Nodup. Inductive case (cons): uw = cons adj rest, so (cons adj rest).append wv = cons adj (rest.append wv). The support is u :: (rest.append wv).support. Nodup of u :: (rest.append wv).support gives Nodup of (rest.append wv).support. Apply the inductive hypothesis to rest and wv.
-/
lemma nodup_suffix_of_append_nodup {u v w : V}
    (uw : G.Walk u w) (wv : G.Walk w v)
    (h : (uw.append wv).support.Nodup) : wv.support.Nodup := by
      -- By definition of `support`, we know that `(uw.append wv).support = uw.support ++ wv.support.tail`.
      have h_support_append : (uw.append wv).support = uw.support ++ wv.support.tail := by
        exact Walk.support_of_append uw wv
      cases wv <;> simp_all +decide [ List.nodup_append ];
      · exact List.nodup_singleton _;
      · cases uw
        · by_contra
          have x := h.2.2 u
          simp at x
          specialize x u this
          contradiction
        · by_contra
          have x := h.2.2 w
          simp at x
          specialize x w this
          contradiction

theorem contains_subwalk {u v w : V} (p : G.Walk u v) (w_in_walk : w ∈ p.support) (w_ne_v : w ≠ v):
    ∃ p' : G.Walk u w, p'.length < p.length ∧ p'.support <+: p.support := by
    by_cases u_eq_w : u = w
    · let w' : G.Walk u u := Walk.nil
      use u_eq_w ▸ w'
      subst u_eq_w
      rw [length_nil_zero]
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
          obtain ⟨p',length_le⟩ := contains_subwalk c w_in_c w_ne_v
          use (Walk.cons b p')
          unfold length
          constructor
          · grind
          · simp_all

/-
PROVIDED SOLUTION
By induction on p. Base case (nil): w ∈ nil.support means w = u, so use nil and nil. Inductive case (cons adj rest : Walk u v with u -adj-> m then rest : Walk m v): w ∈ (cons adj rest).support means w = u or w ∈ rest.support. If w = u, use nil and (cons adj rest). If w ∈ rest.support, use the IH on rest to get mw and wv with mw.append wv = rest, then use (cons adj mw) and wv.
-/
theorem split_at {u v w : V} (p : G.Walk u v) (w_in_walk : w ∈ p.support):
    ∃ uw : G.Walk u w, ∃ wv : G.Walk w v, uw.append wv = p := by
    have h_length : ∀ {u v : V}, ∀ p : G.Walk u v, ∀ w ∈ p.support, ∃ uw : G.Walk u w, ∃ wv : G.Walk w v, uw.append wv = p := by
      intros u v p w hw
      induction p generalizing w
      · cases hw
        · exists Walk.nil, Walk.nil
        · contradiction
      · rename_i h p w_in_walk
        cases hw;
        · exact ⟨ Walk.nil, Walk.cons h p, by rfl ⟩
        · obtain ⟨ uw, wv, hw ⟩ := w_in_walk _ ‹_›
          use cons h uw, wv; simp [Walk.append, hw]
    exact h_length p w w_in_walk


end Walk

/-- A `path` is a walk with no repeating vertices. -/
abbrev Path (u v : V) := { p : G.Walk u v // List.Nodup p.support }

def nil_path (u : V) : G.Path u u :=
  let w : G.Walk u u := Walk.nil
  have p : List.Nodup w.support := by
    unfold w
    unfold Walk.support
    simp
  ⟨ w, p ⟩

namespace Path

theorem nil_path_eq {u v: V} (h : u = v): G.nil_path u = h ▸ G.nil_path v := by
  subst h
  simp_all only

@[simp]
def length {u v : V} (p : G.Path u v) : ℕ := p.1.length

@[simp]
theorem length_same {u v : V} (p : G.Path u v):
    p.length = p.val.length := by unfold length ; rfl

@[simp]
theorem length_nil_zero {u : V} : (G.nil_path u).length  = 0 := by
  unfold length nil_path
  simp_all

@[simp]
theorem length_nil_walk_zero {u : V} : (G.nil_path u).val.length  = 0 := by
  unfold Walk.length nil_path
  simp_all

@[simp]
theorem support_walk_nodup {u : V} : (G.nil_path u).val.support.Nodup := by
  unfold Walk.support nil_path
  simp_all

theorem length_diff_ends_ne_zero {u v : V} (h : u ≠ v) (p : G.Path u v):
    p.length > 0 := by
  unfold length
  apply Walk.length_diff_ends_ne_zero
  exact h

@[simp]
def support {u v : V} (p : G.Path u v) : List V := p.1.support

@[simp]
theorem nil_support {u : V} (p : G.Path u u) : p.support = [u] := by simp [p.prop]

@[simp]
theorem goal_in_support (p: G.Path u v): v ∈ p.support := by simp


theorem path_support_length_le {u v : V} (p : G.Path u v) :
    p.val.support.length ≤ Fintype.card V := List.Nodup.length_le_card p.prop

theorem path_length_lt_card
    {u v : V} (p : G.Path u v) : p.val.length < Fintype.card V := by
  have h_len := p.val.walk_support_length
  have h_le := path_support_length_le p
  rw [h_len] at h_le
  exact Nat.lt_of_succ_le h_le

/-- Take a uv path `p :Path G u v`, a proof `h : G.Adj v w` that a vw edge exists
and a proof `proof_w_not_in_support : w ∉ support G p.walk` that w is not part of
the path yet and return a path extended by w. -/
def concat (p : G.Path u v) (h : G.Adj v w) (proof_w_not_in_support : w ∉ p.val.support) :
    G.Path u w :=
  let path_walk := p.val.concat h
  let set_eq : path_walk.support = p.val.support ++ [w] := by simp [path_walk]
  let path_nodup : List.Nodup path_walk.support := by
    simp [List.Nodup]
    rw [set_eq]
    rw [List.pairwise_append_comm]
    · simp only [List.cons_append, List.nil_append, List.pairwise_cons]
      apply And.intro
      · intro a ha wa; simp_all only [not_true_eq_false]
      · exact p.prop
      -- we need to prove that the ≠ function that occurs in nodup is symmetric
      -- (otherwise one of our helper theorems does not hold any more)
    · intro x y notEq h
      apply notEq
      rw [h]
  ⟨ path_walk, path_nodup ⟩

def append {u v w : V} (uv : G.Path u v) (vw : G.Path v w) (h : ∀ a ∈ uv.val.support, ∀ b ∈ vw.val.support.tail, a ≠ b): G.Path u w :=
  let uwWalk : G.Walk u w := uv.val.append vw.val
  have noDup : List.Nodup uwWalk.support := by
    unfold uwWalk
    rw [Walk.support_of_append]
    apply List.nodup_append.mpr
    and_intros
    · exact uv.prop
    · grind
    · exact h
  ⟨ uwWalk, noDup ⟩

/-- Definition of `Shortest Path` -/
def is_shortest {u v : V} (p : G.Path u v) : Prop :=
  ∀ p' : G.Path u v, p.length ≤ p'.length

def is_prefix {u v w : V} (p : G.Path u v) (p' : G.Path u w) : Bool :=
  p.val.is_prefix p'.val

@[simp]
theorem support_concat_is_append_at_end (p: G.Path u v) (h: G.Adj v w)(proof_w_not_in_support : w ∉ p.val.support):
   (p.concat h proof_w_not_in_support).support = p.support ++ [w] := by simp [concat]

@[simp]
theorem concat_inc_length_by_one (p : G.Path u v) (h : G.Adj v w) (proof_w_not_in_support : w ∉ p.support) :
      (p.concat h proof_w_not_in_support).length = 1 + p.length := by
  apply Walk.concat_inc_length_by_one

theorem split_at_end (p : G.Path u v) (not_nil : u ≠ v):
    ∃ w : V, ∃ p' : G.Path u w, ∃ w_adj_v : G.Adj w v,
      v ∉ p'.support ∧ p.val = p'.val.concat w_adj_v := by
    obtain ⟨ w, p_w, w_adj_v, walk_extended ⟩ := p.val.split_at_end not_nil

    have supp_compose : p.support = p_w.support ++ [v] := by simp [walk_extended]

    have nodup : p_w.support.Nodup := by
      have h : (p.support).Nodup := p.prop
      rw [supp_compose] at h
      apply List.pairwise_append.mp at h
      grind
    use w
    use⟨ p_w, nodup ⟩
    use w_adj_v
    have not_in_supp : v ∉ p_w.support:= by
      have support_compose : p.val.support= p_w.support ++ [v] := by simp [walk_extended]
      have p_supp_nodup : p.val.support.Nodup := p.prop
      rw [support_compose] at p_supp_nodup
      apply List.pairwise_append.mp at p_supp_nodup
      grind
    use not_in_supp

/-
PROVIDED SOLUTION
Use `split_at_end p not_nil` to obtain ⟨w, p', w_adj_v, _, _⟩. Then return ⟨w, ⟨p', w_adj_v⟩⟩.

Induction on p.val (the underlying walk). p.val can't be nil since u ≠ v. So p.val = Walk.cons adj rest. If rest is nil, then return ⟨u, nil_path u, adj⟩. Otherwise, recursively call snoc on the tail (which is a path since prefix of a nodup list is nodup), then prepend the first edge.

Alternative simpler approach: use Walk.snoc p.val not_nil to get ⟨w, ⟨walk, adj⟩⟩. Then show walk.support is nodup because it's a sublist of p.val.support (which is nodup). The key is that walk.support ++ [v] = p.val.support (by the concatenation property of Walk.snoc/split_at_end).
-/
def snoc (p : G.Path u v) (not_nil : u ≠ v):
    Σ w : V, { _p' : G.Path u w // G.Adj w v } :=
  let len_pos : p.val.length > 0 := Walk.length_diff_ends_ne_zero not_nil p.val
  let ⟨w, walk, ⟨adj, concat_eq⟩⟩ := p.val.snoc_with_proof len_pos
  have walk_nodup : walk.support.Nodup := by
    have h : (walk.concat adj).support.Nodup := concat_eq ▸ p.prop
    rw [Walk.support_concat_is_append_at_end] at h
    exact (List.nodup_append.mp h).1
  ⟨w, ⟨⟨walk, walk_nodup⟩, adj⟩⟩

theorem contains_subpath {u v w : V} (p : G.Path u v) (w_in_path : w ∈ p.support) (w_ne_v : w ≠ v):
    ∃ p' : G.Path u w, p'.length  < p.length := by
    obtain ⟨w',len,supp⟩ := p.val.contains_subwalk w_in_path w_ne_v
    have p_nodup : w'.support.Nodup := by
      apply List.Nodup.sublist (l₂ := p.support)
      · apply List.IsPrefix.sublist
        exact supp
      · exact p.prop
    use ⟨ w', p_nodup⟩
    unfold length
    apply len



end Path


def distance_is (u v : V) (dist: ℕ) : Prop :=
  (∃ p : G.Path u v, p.length = dist ∧ p.is_shortest)

def distance_ge (u v : V) (dist: ℕ) : Prop :=
  ∀ p : G.Path u v, p.length ≥ dist

def distance_gt (u v : V) (dist: ℕ) : Prop :=
  ∀ p : G.Path u v, p.length > dist

def distance_lt (u v : V) (dist: ℕ) : Prop :=
  ∃ p : G.Path u v, p.length < dist

lemma distance_ge_lt (u v : V) (d1 d2: ℕ) :
    G.distance_ge u v d1 ∧ d2 ≤ d1 → G.distance_ge u v d2 := by
    unfold WeightedDiGraph.distance_ge
    simp_all
    intro ge_d1 d2_le_d1 p p_nodup
    apply le_trans
    · exact d2_le_d1
    · exact ge_d1 p p_nodup


namespace Walk

/- Copied from Mathlib -/
theorem mem_support_nil_iff {u v : V}: u ∈ (Walk.nil : G.Walk v v).support  ↔ u = v := by
  apply Iff.intro
  · intro u_in_supp
    unfold Walk.support at u_in_supp
    simp_all
  · intro u_eq_v
    unfold Walk.support
    simp_all

/- Copied from Mathlib -/
/-- Given a vertex in the support of a path, give the path from (and including) that vertex to
the end. In other words, drop vertices from the front of a path until (and not including)
that vertex. -/
def dropUntil {v w : V} : ∀ (p : G.Walk v w) (u : V), u ∈ p.support → G.Walk u w
  | Walk.nil, u, h => by
    --rw [mem_support_nil_iff.mp h]
    have u_eq_v : u = v := by
      apply mem_support_nil_iff.mp
      exact h
    use u_eq_v ▸ Walk.nil
  | Walk.cons r p, u, h =>
    if hx : v = u then by
      subst u
      exact Walk.cons r p
    else dropUntil p u <| by
      cases h
      · exact (hx rfl).elim
      · assumption

lemma walk_trans (h : G.Adj u u') (w' : G.Walk u' v)  :
  ∀ (u_eq_v : u = v),
  u_eq_v ▸ Walk.nil = Walk.cons h w' → ⊥ := by
    intro u_eq_v
    subst u_eq_v
    grind

@[simp]
lemma support_Drop_Until_Suffix (w : G.Walk u v) (u : V) (u_in_supp : u ∈ w.support):
  (w.dropUntil u u_in_supp).support <:+ w.support := by
  induction w with
  | nil =>
    unfold dropUntil support
    split
    · next nil_eq_cons =>
      simp at nil_eq_cons
      exfalso
      apply walk_trans (V:=V)
      apply nil_eq_cons
    · simp
  | cons h w' ih =>
    unfold dropUntil
    split
    · simp
      rename_i h_1
      subst h_1
      simp_all only [support_cons, List.suffix_rfl]
    · conv =>
        right
        unfold support
      grind

@[simp]
theorem dropUntilMakesShorter (p : G.Walk u v) (f : V) (h : f ∈ p.support):
  (p.dropUntil f h).length ≤ p.length := by
  induction p with
  | nil =>
    unfold length dropUntil
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


/-- Given a walk, produces a walk from it by bypassing subwalks between repeated vertices.
The result is a path, as shown in `SimpleGraph.Walk.bypass_isPath`.
This is packaged up in `SimpleGraph.Walk.toPath`. -/
def bypass {u v : V} : G.Walk u v → G.Walk u v
  | Walk.nil => Walk.nil
  | Walk.cons ha p =>
    let p' := bypass p
    if hs : u ∈ p'.support then
      p'.dropUntil u hs
    else
      Walk.cons ha p'

@[simp]
theorem nil_bypass {u : V} : (Walk.nil : G.Walk u u).bypass = (Walk.nil : G.Walk u u) := by unfold bypass ; rfl


theorem bypass_isPath (p : G.Walk u v) : p.bypass.support.Nodup := by
  induction p with
  | nil => simp!
  | cons h p' ih =>
    simp only [Walk.bypass]
    split_ifs with hs
    · next f w t =>
      have suff : (p'.bypass.dropUntil f hs).support <:+ p'.bypass.support := by simp
      grind
    · unfold Walk.support
      simp
      constructor
      · exact hs
      · exact ih

theorem length_bypass_le (p : G.Walk u v) : p.bypass.length ≤ p.length:= by
  induction p with
  | nil =>
    unfold bypass length
    rfl
  | cons f_adj_t p' ih =>
    unfold bypass
    simp_all
    split
    · conv =>
        right
        unfold length
      trans
      · apply dropUntilMakesShorter
      · grind
    · unfold length
      grind

theorem shorter_path_exists (w : G.Walk u v):
  ∃ p : G.Path u v, p.length ≤ w.length := by
  let w' : G.Walk u v := w.bypass
  have nodup : w'.support.Nodup := by unfold w' ; apply bypass_isPath
  use ⟨ w', nodup ⟩
  unfold Path.length
  apply length_bypass_le

lemma append_support_prefix {a b c: V} (w : G.Walk a b) (w' : G.Walk b c):
    w.support <+: (w.append w').support := by
    cases compose : w
    · unfold Walk.support Walk.append
      split <;> simp
    case cons a' h p =>
      unfold Walk.support Walk.append
      simp
      apply Walk.append_support_prefix

lemma concat_support_prefix {a b c: V} (w : G.Walk a b) (adj : G.Adj b c):
    w.support <+: (w.concat adj).support := by
    unfold Walk.concat
    apply Walk.append_support_prefix

lemma append_support_suffix {a b c: V} (w : G.Walk a b) (w' : G.Walk b c):
    w'.support <:+ (w.append w').support := by
    cases compose : w
    · unfold Walk.support Walk.append
      split <;> simp
    case cons a' h p =>
      conv =>
        right ; unfold Walk.support Walk.append
      simp
      apply List.suffix_cons_iff.mpr
      right
      apply Walk.append_support_suffix

lemma recompose {s v u: V} (p : G.Walk s v) (u_on_p : u ∈ p.support) (u_ne_v : u ≠ v):
  ∃ u' : V, ∃ s_u : G.Walk s u, ∃ adj_u_u' : G.Adj u u', ∃ u'_v : G.Walk u' v,
    p = (s_u.concat adj_u_u').append u'_v := by
    cases compose : p
    · rw [compose] at u_on_p
      unfold Walk.support at u_on_p
      simp at u_on_p
      contradiction
    case cons w h p' =>
      by_cases s_eq_u : s = u
      · subst s_eq_u
        use w
        use Walk.nil
        use h
        use p'
        unfold Walk.concat Walk.append Walk.append
        simp
      · have u_on_p' : u ∈ p'.support := by
          rw [compose] at u_on_p
          unfold Walk.support at u_on_p
          apply List.mem_cons.mp at u_on_p
          cases u_on_p
          case inl h =>
            apply absurd h.symm s_eq_u
          case inr h =>
            exact h
        obtain ⟨u',w_u,adj_w_u',u'_v,prop⟩ := Walk.recompose p' u_on_p' u_ne_v
        use u'
        use (Walk.cons h w_u)
        use adj_w_u'
        use u'_v
        rw [prop]
        conv =>
          right
          unfold Walk.concat
          left
          unfold Walk.append
        rfl

end Walk

/-- Given an s v path and a node u on that path and the fact that u is not v, split the path
into three parts: the path from s to u, the edge u u', and a path from u' to v. -/
lemma Path.recompose {s v u: V} (p : G.Path s v) (u_on_p : u ∈ p.support) (u_ne_v : u ≠ v):
    ∃ u' : V, ∃ s_u : G.Path s u, ∃ adj_u_u' : G.Adj u u', ∃ u'_v : G.Path u' v,
      ∃ u'_supp : u' ∉ s_u.val.support,
      ∃ u'_v_path_supp : (∀ a ∈ (s_u.concat adj_u_u' u'_supp).val.support, ∀ b ∈ u'_v.val.support.tail, a ≠ b),
      p = (s_u.concat adj_u_u' u'_supp).append u'_v u'_v_path_supp := by
        obtain ⟨ u', w_s_u, adj_u_u', w_u'_v, compose⟩ := p.val.recompose u_on_p u_ne_v
        use u'
        have s_u_nodup : w_s_u.support.Nodup := by
          apply List.Sublist.nodup ; rotate_left
          · exact p.prop
          · rw [compose]
            apply List.IsPrefix.sublist
            apply List.IsPrefix.trans ; rotate_left
            · apply Walk.append_support_prefix
            · apply Walk.concat_support_prefix
        use ⟨w_s_u,s_u_nodup⟩
        use adj_u_u'
        have u'_v_nodup : w_u'_v.support.Nodup := by
          apply List.Sublist.nodup ; rotate_left
          · exact p.prop
          · rw [compose]
            apply List.IsSuffix.sublist
            apply Walk.append_support_suffix
        use ⟨w_u'_v, u'_v_nodup⟩
        have u'_supp : u' ∉ w_s_u.support := by
          by_contra u'_in_w_s_u
          obtain ⟨walk,prop⟩ := p
          simp at compose
          rw [compose] at prop
          rw [Walk.support_of_append] at prop
          apply List.nodup_append.mp at prop
          obtain ⟨prop,_,_⟩ := prop
          unfold Walk.concat at prop
          rw [Walk.support_of_append] at prop
          apply List.nodup_append.mp at prop
          obtain ⟨_,_,prop⟩ := prop
          specialize prop u' u'_in_w_s_u u'
          simp at prop
        use u'_supp
        have u'_v_path_supp : ∀ a ∈ (concat ⟨w_s_u, s_u_nodup⟩ adj_u_u' u'_supp).val.support, ∀ b ∈ w_u'_v.support.tail, a ≠ b := by
          intro a a_in b b_in
          obtain ⟨ walk, prop ⟩ := p
          simp at compose
          rw [compose] at prop
          rw [Walk.support_of_append] at prop
          apply List.nodup_append.mp at prop
          obtain ⟨ _,_,prop ⟩ := prop
          specialize prop a a_in b b_in
          exact prop
        use u'_v_path_supp
        unfold Path.concat Path.append
        simp
        ext
        rw [compose]

lemma Walk.internal_contact_to_cons_walk {s v u : V}
  (s_u : G.Walk s u)
  (adj_u_u' : G.Adj u u')
  (u'_v : G.Walk u' v):
  (s_u.concat adj_u_u').append u'_v = s_u.append (Walk.cons adj_u_u' u'_v) := by
    cases compose : s_u
    · unfold Walk.concat Walk.append
      unfold Walk.append
      simp only
    case cons w h p =>
      unfold Walk.concat
      conv => left ; left ; unfold Walk.append
      conv => right ; unfold Walk.append
      nth_rw 1 [Walk.append]
      congr 1
      conv => right ; rw [← Walk.internal_contact_to_cons_walk]
      unfold Walk.concat
      rfl

end WeightedDiGraph

-- tests
example : WeightedDiGraph (Fin 3) (Nat) where
  Adj := fun f t =>
    match (f,t) with
     | (0,1) => true
     | (1,2) => true
     | (2,1) => true
     | (_,_) => false
  Payload := fun f t h => by
      by_cases hf0: f = 0
      <;> by_cases hf1: f = 1
      <;> by_cases hf2: f = 2
      <;> by_cases ht0: t = 0
      <;> by_cases ht1: t = 1
      <;> by_cases ht2: t = 2
      -- now we have 64 goals
      <;> try omega
      all_goals simp_all
      exact 3 -- 0 1 edge
      exact 4 -- 1 2 edge
      exact 5 -- 2 1 edge

  instDecAdj := fun a b => by
    simp
    obtain ⟨ va, lta ⟩ := a
    obtain ⟨ vb, ltb ⟩ := b
    cases va
    case zero =>
      cases vb
      case zero => simp; exact instDecidableFalse
      case succ n =>
        cases n
        case zero => simp; exact instDecidableTrue
        case succ n' => simp; exact instDecidableFalse
    case succ n =>
      cases vb
      case zero => simp; exact instDecidableFalse
      case succ nb =>
        cases n
        case zero =>
          simp
          cases nb
          case zero => simp; exact instDecidableFalse
          case succ nb'' =>
            cases nb''
            case zero => simp; exact instDecidableTrue
            case succ nb3 => simp; exact instDecidableFalse
        case succ n' =>
          cases n'
          case succ n'' => simp; exact instDecidableFalse
          case zero =>
            simp
            cases nb
            case zero => simp; exact instDecidableTrue
            case succ x => simp; exact instDecidableFalse
