import SearchAlgorithms.SearchAlgorithm

/-!
# Linear-time path reconstruction

`WeightedDiGraph.extract_path_to` rebuilds the path to the goal from the mother pointers by
*appending* one edge at the end of the path built so far (`Walk.concat`, i.e. `Walk.append` of
the whole prefix).  That is `Θ(L²)` for a path with `L` edges, and it is the one remaining
super-linear cost of all the search implementations in this library: the search itself is
linear in the number of expansions, but a run whose answer is a long path spends most of its
time in the reconstruction (see the measurements in `BenchHeapLazy`).

This module adds a **linear** reconstruction with exactly the same result.  The idea is to
follow the mother pointers from the goal backwards, as `extract_path_to` does, but to grow the
walk at its *front*: `Walk.cons` is `O(1)`, so the whole reconstruction is `O(L)`.  Concretely,
`extract_walk_fast` carries an accumulator `acc : G.Walk v goal` (the part of the answer that
is already built) and replaces `v` by its mother.

* `extract_walk_fast_eq` — the accumulator version computes
  `(extract_path_to start v …).1.val.append acc`;
* `extract_path_fast`, `extract_path_fast_eq` — hence, started with the empty accumulator at
  the goal, it computes literally the path of `extract_path_to`.  The `Nodup` proof of the
  returned `Path` is taken from that equality, so nothing is recomputed at run time (proofs
  are erased).

Because the result is *the same path*, no statement about the searches has to be re-proved:
`SearchAlgorithms.SearchExeFast` plugs this reconstruction into the search driver and shows
the driver returns the same `Option (Path start goal)`.
-/

namespace WeightedDiGraph

variable {V : Type} {E : Type} [FinEnum V]
variable {G : WeightedDiGraph V E}
variable {D : Type} [FValueComp D]

namespace Walk

/-- Appending the empty walk changes nothing. -/
theorem append_nil {u v : V} (p : G.Walk u v) : p.append Walk.nil = p := by
  induction p with
  | nil => rfl
  | cons h p ih => simp only [Walk.append, ih]

/-- `Walk.append` is associative. -/
theorem append_assoc {u v w x : V} (p : G.Walk u v) (q : G.Walk v w) (r : G.Walk w x) :
    (p.append q).append r = p.append (q.append r) := by
  induction p with
  | nil => rfl
  | cons h p ih => simp only [Walk.append, ih]

/-- Appending a walk to an edge that is concatenated at the end: the edge moves to the front
of the appended walk.  This is the step that turns the quadratic `concat` chain of
`extract_path_to` into a linear `cons` chain. -/
theorem concat_append {u v w x : V} (p : G.Walk u v) (h : G.Adj v w) (r : G.Walk w x) :
    (p.concat h).append r = p.append (Walk.cons h r) := by
  unfold Walk.concat
  rw [append_assoc]
  rfl

end Walk

/-- **Linear-time reconstruction of the path to `v`.**

`acc : G.Walk v goal` is the part of the answer that is already built; the function walks from
`v` back to `start` along the mother pointers and prepends one edge per step (`O(1)` each), so
reconstructing a path of `L` edges costs `O(L)` instead of the `Θ(L²)` of `extract_path_to`.

The invariants are exactly those of `extract_path_to`: the mother of a visited vertex is
visited (`mother_invar`), it is adjacent to it (`mother_invar_adj`), and its path order is
smaller (`decreasing_invar`), which is what makes the recursion terminate. -/
def extract_walk_fast (start : V) (goal : V) (s : base_search_state G D)
    (mother_invar : search_invar_mother_is_visited s)
    (mother_invar_adj : search_invar_mother_is_adjacent start s)
    (decreasing_invar : search_invar_mother_decreasing_path_order start s)
    (v : V) (hv : v ∈ s.visited) (acc : G.Walk v goal) : G.Walk start goal :=
  if hstart : v = start then hstart ▸ acc
  else
    extract_walk_fast start goal s mother_invar mother_invar_adj decreasing_invar
      (s.mother ⟨v, hv⟩) (mother_invar ⟨v, hv⟩)
      (Walk.cons (mother_invar_adj ⟨v, hv⟩ hstart) acc)
termination_by FValueComp.wf.wrap (s.pathOrder v)
decreasing_by
  simp_all

/-- One step of `extract_path_to`: the path to a vertex other than `start` is the path to its
mother with the mother edge concatenated at the end. -/
theorem extract_path_to_step (start : V) (s : base_search_state G D)
    (mother_invar : search_invar_mother_is_visited s)
    (mother_invar_adj : search_invar_mother_is_adjacent start s)
    (decreasing_invar : search_invar_mother_decreasing_path_order start s)
    (v : V) (hv : v ∈ s.visited) (hne : ¬ v = start) :
    (extract_path_to start v s hv mother_invar mother_invar_adj decreasing_invar).1.val
      = ((extract_path_to start (s.mother ⟨v, hv⟩) s (mother_invar ⟨v, hv⟩) mother_invar
          mother_invar_adj decreasing_invar).1.val).concat (mother_invar_adj ⟨v, hv⟩ hne) := by
  rw [extract_path_to]
  simp only [dif_neg hne]
  rfl

/-- **The fast reconstruction computes the walk of `extract_path_to`**, with the accumulator
appended at the end.  Everything that is known about `extract_path_to` therefore holds for it;
in particular the walk it returns for the empty accumulator is a path. -/
theorem extract_walk_fast_eq (start : V) (goal : V) (s : base_search_state G D)
    (mother_invar : search_invar_mother_is_visited s)
    (mother_invar_adj : search_invar_mother_is_adjacent start s)
    (decreasing_invar : search_invar_mother_decreasing_path_order start s)
    (v : V) (hv : v ∈ s.visited) (acc : G.Walk v goal) :
    extract_walk_fast start goal s mother_invar mother_invar_adj decreasing_invar v hv acc
      = (extract_path_to start v s hv mother_invar mother_invar_adj
          decreasing_invar).1.val.append acc := by
  induction v, hv, acc using extract_walk_fast.induct start goal s mother_invar mother_invar_adj
      decreasing_invar with
  | case1 hv acc =>
      rw [extract_walk_fast, extract_path_to]
      simp only [dif_pos]
      rfl
  | case2 v hv acc hne ih =>
      rw [extract_path_to_step start s mother_invar mother_invar_adj decreasing_invar v hv hne,
        Walk.concat_append, extract_walk_fast]
      simp only [dif_neg hne]
      exact ih

/-- **The path to `goal`, reconstructed in linear time.**  The `Nodup` proof is inherited from
`extract_path_to` through `extract_walk_fast_eq`, so it costs nothing at run time. -/
def extract_path_fast (start : V) (goal : V) (s : base_search_state G D)
    (goal_reached : goal ∈ s.visited)
    (mother_invar : search_invar_mother_is_visited s)
    (mother_invar_adj : search_invar_mother_is_adjacent start s)
    (decreasing_invar : search_invar_mother_decreasing_path_order start s) :
    G.Path start goal :=
  ⟨extract_walk_fast start goal s mother_invar mother_invar_adj decreasing_invar goal
      goal_reached Walk.nil, by
    rw [extract_walk_fast_eq, Walk.append_nil]
    exact (extract_path_to start goal s goal_reached mother_invar mother_invar_adj
      decreasing_invar).1.prop⟩

/-- **`extract_path_fast` returns literally the path of `extract_path_to`.** -/
theorem extract_path_fast_eq (start : V) (goal : V) (s : base_search_state G D)
    (goal_reached : goal ∈ s.visited)
    (mother_invar : search_invar_mother_is_visited s)
    (mother_invar_adj : search_invar_mother_is_adjacent start s)
    (decreasing_invar : search_invar_mother_decreasing_path_order start s) :
    extract_path_fast start goal s goal_reached mother_invar mother_invar_adj decreasing_invar
      = (extract_path_to start goal s goal_reached mother_invar mother_invar_adj
          decreasing_invar).1 := by
  apply Subtype.ext
  show extract_walk_fast start goal s mother_invar mother_invar_adj decreasing_invar goal
      goal_reached Walk.nil = _
  rw [extract_walk_fast_eq, Walk.append_nil]

end WeightedDiGraph
