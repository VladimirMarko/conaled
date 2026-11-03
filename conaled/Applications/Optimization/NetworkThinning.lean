import Applications.Optimization.NetworkPaths
import Applications.Optimization.Thinning

/-!
# The actual adjacent-thinning minimum network path

The empty path has an explicit absent source.  This totalizes the source's
`head` selector.  Every comparison made after a nonempty layer is between
nonempty paths, where the relation is exactly the printed relation.
-/

namespace Optimization.NetworkThinning

open NetworkPaths

def firstSource : Path → Option Int
  | [] => none
  | e :: _ => some e.source

def Dominates (p q : Path) : Prop := firstSource p = firstSource q ∧ cost p ≤ cost q

instance : DecidableRel Dominates := fun _ _ => inferInstanceAs (Decidable (_ ∧ _))

theorem dominates_refl (p : Path) : Dominates p p := ⟨rfl, Int.le_refl _⟩

theorem dominates_trans (p q r : Path) (hpq : Dominates p q) (hqr : Dominates q r) :
    Dominates p r := ⟨hpq.1.trans hqr.1, Int.le_trans hpq.2 hqr.2⟩

theorem dominates_nonempty (e f : Edge) (p q : Path) :
    Dominates (e :: p) (f :: q) ↔
      e.source = f.source ∧ cost (e :: p) ≤ cost (f :: q) := by
  simp [Dominates, firstSource]

theorem dominates_nil_left (p : Path) : Dominates [] p ↔ p = [] := by
  cases p <;> simp [Dominates, firstSource]

theorem dominates_nil_right (p : Path) : Dominates p [] ↔ p = [] := by
  cases p <;> simp [Dominates, firstSource]

theorem linked_mono (e : Edge) (p q : Path) (h : Dominates p q)
    (hq : linked e q = true) : linked e p = true := by
  cases p with
  | nil => rfl
  | cons f p =>
      cases q with
      | nil => simp [Dominates, firstSource] at h
      | cons g q =>
          have hs : f.source = g.source := Option.some.inj h.1
          simpa only [linked, hs] using hq

theorem cons_mono (e : Edge) (p q : Path) (h : Dominates p q) :
    Dominates (e :: p) (e :: q) := by
  refine ⟨rfl, ?_⟩
  simpa only [cost_cons] using Int.add_le_add_left h.2 e.weight

/-- The context-sensitive map equivalence has the uniform suffix-length domain
actually established by layered path generation. -/
theorem cons_dominance_iff (e : Edge) (p q : Path)
    (hlen : p.length = q.length) (hp : linked e p = true) (hq : linked e q = true) :
    Dominates (e :: p) (e :: q) ↔ Dominates p q := by
  cases p with
  | nil =>
      have hqn : q = [] := by simpa using hlen.symm
      subst q
      simp [Dominates, firstSource]
  | cons f p =>
      cases q with
      | nil => simp at hlen
      | cons g q =>
          have hs : f.source = g.source := by
            simp only [linked, beq_iff_eq] at hp hq
            exact hp.symm.trans hq
          simp only [Dominates, firstSource, hs, true_and, cost_cons]
          omega

theorem thinning_append (xs ys us vs : List Path)
    (hx : Thinning.IsThinning Dominates xs us) (hy : Thinning.IsThinning Dominates ys vs) :
    Thinning.IsThinning Dominates (xs ++ ys) (us ++ vs) := by
  refine ⟨hx.1.append hy.1, ?_⟩
  intro p hp
  rcases List.mem_append.mp hp with hp | hp
  · obtain ⟨q, hq, hqp⟩ := hx.2 p hp
    exact ⟨q, List.mem_append_left _ hq, hqp⟩
  · obtain ⟨q, hq, hqp⟩ := hy.2 p hp
    exact ⟨q, List.mem_append_right _ hq, hqp⟩

theorem cons_thinning (e : Edge) (ps qs : List Path)
    (h : Thinning.IsThinning Dominates ps qs) :
    Thinning.IsThinning Dominates ((ps.filter (linked e)).map (e :: ·))
      ((qs.filter (linked e)).map (e :: ·)) := by
  apply Thinning.thinning_map Dominates Dominates (e :: ·) (cons_mono e)
  exact Thinning.thinning_filter Dominates (linked e) (linked_mono e) ps qs h

theorem step_thinning (es : List Edge) (ps qs : List Path)
    (h : Thinning.IsThinning Dominates ps qs) :
    Thinning.IsThinning Dominates (step es ps) (step es qs) := by
  induction es with
  | nil => exact Thinning.thinning_refl Dominates dominates_refl []
  | cons e es ih => exact thinning_append _ _ _ _ (cons_thinning e ps qs h) ih

theorem mem_step_iff (es : List Edge) (ps : List Path) (p : Path) :
    p ∈ step es ps ↔ ∃ e ∈ es, ∃ q ∈ ps, linked e q = true ∧ p = e :: q := by
  simp only [step, List.mem_flatMap, List.mem_map, List.mem_filter]
  constructor
  · rintro ⟨e, he, q, ⟨hq, hl⟩, hp⟩
    exact ⟨e, he, q, hq, hl, hp.symm⟩
  · rintro ⟨e, he, q, hq, hl, hp⟩
    exact ⟨e, he, q, ⟨hq, hl⟩, hp.symm⟩

theorem compared_candidates_nonempty (es : List Edge) (ps : List Path)
    (p : Path) (hp : p ∈ step es ps) : p ≠ [] := by
  obtain ⟨e, _, q, _, _, rfl⟩ := (mem_step_iff es ps p).mp hp
  simp

def tstep (es : List Edge) (ps : List Path) : List Path :=
  Thinning.thinBy Dominates (step es ps)

def thinnedPaths (ns : Net) : List Path := ns.foldr tstep [[]]

def mcp (ns : Net) : Option Path := Thinning.argmin cost (thinnedPaths ns)

def Optimal (ns : Net) (p : Path) : Prop :=
  Feasible ns p ∧ ∀ q, Feasible ns q → cost p ≤ cost q

theorem thinnedPaths_refinement (ns : Net) :
    Thinning.IsThinning Dominates (paths ns) (thinnedPaths ns) := by
  exact Thinning.pruneFold_thinning Dominates dominates_refl dominates_trans step
    (Thinning.thinBy Dominates) step_thinning
    (Thinning.thinBy_correct Dominates dominates_refl dominates_trans) [[]] ns

theorem thinnedPaths_feasible (ns : Net) (p : Path) (hp : p ∈ thinnedPaths ns) :
    Feasible ns p :=
  (paths_mem_iff ns p).mp ((thinnedPaths_refinement ns).1.subset hp)

theorem thinnedPaths_length (ns : Net) (p : Path) (hp : p ∈ thinnedPaths ns) :
    p.length = ns.length := feasible_length ns p (thinnedPaths_feasible ns p hp)

theorem mcp_optimal (ns : Net) (p : Path) (h : mcp ns = some p) : Optimal ns p := by
  have hm := Thinning.minimizer_of_represents (thinnedPaths_refinement ns).represents
    cost (fun _ _ _ _ hpq => hpq.2) (Thinning.argmin_correct cost _ p h)
  exact ⟨(paths_mem_iff ns p).mp hm.1,
    fun q hq => hm.2 ((paths_mem_iff ns q).mpr hq)⟩

theorem mcp_mem_paths (ns : Net) (p : Path) (h : mcp ns = some p) : p ∈ paths ns :=
  (paths_mem_iff ns p).mpr (mcp_optimal ns p h).1

theorem mcp_none_iff (ns : Net) : mcp ns = none ↔ ¬ ∃ p, Feasible ns p := by
  rw [mcp, Thinning.argmin_eq_none_iff]
  rw [Thinning.thinning_empty_iff Dominates _ _ (thinnedPaths_refinement ns)]
  constructor
  · intro he hn
    exact ((paths_nonempty_iff ns).mpr hn) he
  · intro hn
    cases he : paths ns with
    | nil => rfl
    | cons p ps =>
        exact False.elim (hn ((paths_nonempty_iff ns).mp (by simp [he])))

theorem mcp_some_iff (ns : Net) : (∃ p, mcp ns = some p) ↔ ∃ p, Feasible ns p := by
  constructor
  · rintro ⟨p, hp⟩
    exact ⟨p, (mcp_optimal ns p hp).1⟩
  · intro h
    cases he : mcp ns with
    | none => exact False.elim ((mcp_none_iff ns).mp he h)
    | some p => exact ⟨p, rfl⟩

theorem mcp_empty_network : mcp [] = some [] := rfl

theorem mcp_empty_layer (ns : Net) : mcp ([] :: ns) = none := rfl

theorem mcp_first_equal_cost :
    mcp [[⟨1, 3, 5⟩, ⟨1, 4, 5⟩]] = some [⟨1, 3, 5⟩] := by decide

theorem different_sources_retained :
    thinnedPaths [[⟨1, 3, 5⟩, ⟨2, 4, 5⟩]] = [[⟨1, 3, 5⟩], [⟨2, 4, 5⟩]] := by decide

theorem single_greedy_path_insufficient :
    mcp [[⟨1, 2, 0⟩], [⟨3, 4, -10⟩, ⟨2, 5, 1⟩]] =
      some [⟨1, 2, 0⟩, ⟨2, 5, 1⟩] ∧
    linked (⟨1, 2, 0⟩ : Edge) [⟨3, 4, -10⟩] = false := by decide

end Optimization.NetworkThinning
