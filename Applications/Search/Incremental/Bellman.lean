import Applications.Search.Incremental.Semantics
import Mathlib.Data.Fintype.Card

/-! Independent Bellman correctness over finite positive rational graphs.
Finite descent is on vertices, not on the non-well-founded rational order. -/
set_option autoImplicit false
set_option warningAsError true
namespace Search.Incremental
variable {n : Nat}

theorem walk_append {w : Graph n} {u v z : Fin n} {a b : ℚ}
    (p : RationalCost.Walk (adjacency w) u v a)
    (q : RationalCost.Walk (adjacency w) v z b) :
    RationalCost.Walk (adjacency w) u z (a+b) := by
  induction p with
  | nil => simpa using q
  | cons edge path ih => simpa [add_assoc] using RationalCost.Walk.cons edge (ih q)

theorem bellman_edge {w : Graph n} (hw : Positive w) {start : Fin n}
    {g : Labels n} (hg : Nonnegative g) (hb : Bellman w start g) (u v : Fin n) :
    g v ≤ g u + w u v := by
  rw [hb v]
  by_cases h : v = start
  · subst v
    simp only [rhsValue_start]
    exact add_nonneg (hg u) (le_of_lt (hw u start))
  · simpa [rhsValue,h] using predecessorMinimum_le w g u v

theorem bellman_walk_le {w : Graph n} (hw : Positive w) {start : Fin n}
    {g : Labels n} (hg : Nonnegative g) (hb : Bellman w start g)
    {u v : Fin n} {c : ℚ} (p : RationalCost.Walk (adjacency w) u v c) :
    g v ≤ g u + (c : Cost) := by
  induction p with
  | nil => simp
  | @cons u v t d c edge path ih =>
    have step := bellman_edge hw hg hb u v
    rw [(edge_iff w u v d).mp edge] at step
    calc
      g t ≤ g v + (c : Cost) := ih
      _ ≤ (g u + (d : Cost)) + (c : Cost) := add_le_add step le_rfl
      _ = g u + ((d+c : ℚ) : Cost) := by simp [add_assoc]

/-- Strict predecessor labels cannot form an infinite chain on finitely many
vertices; no bound on rational denominators is needed. -/
theorem bellman_attains {w : Graph n} (hw : Positive w) {start : Fin n}
    {g : Labels n} (hb : Bellman w start g) (v : Fin n) (q : ℚ) (hv : g v = (q : Cost)) :
    RationalCost.Walk (adjacency w) start v q := by
  let R : Fin n → Fin n → Prop := fun u v => g u < g v
  let : IsTrans (Fin n) R := ⟨fun _ _ _ a b => lt_trans a b⟩
  let : Std.Irrefl R := ⟨fun _ h => lt_irrefl _ h⟩
  have wf := Finite.wellFounded_of_trans_of_irrefl R
  induction v using wf.induction generalizing q with
  | h v ih =>
    by_cases vs : v = start
    · subst v
      have eq : q = 0 := by
        have zero : g start = 0 := by simpa using hb start
        rw [zero] at hv
        exact_mod_cast hv.symm
      subst q
      exact .nil start
    · have bv : g v = predecessorMinimum w g v := by simpa [rhsValue,vs] using hb v
      obtain ⟨u,_,hu⟩ := Finset.exists_mem_eq_inf Finset.univ
        (Finset.univ_nonempty_iff.mpr ⟨start⟩) (fun u => g u + w u v)
      have sum : g u + w u v = (q : Cost) := hu.symm.trans (bv.symm.trans hv)
      cases gu : g u using WithTop.recTopCoe with
      | top => simp [gu] at sum
      | coe a =>
        cases edge : w u v using WithTop.recTopCoe with
        | top => simp [edge] at sum
        | coe b =>
          have pos : 0 < b := by exact_mod_cast (show (0 : Cost) < (b : Cost) by simpa [edge] using hw u v)
          have eq : a+b = q := by
            rw [gu,edge,← WithTop.coe_add] at sum
            exact WithTop.coe_injective sum
          have less : R u v := by
            change g u < g v
            rw [gu,hv]
            exact_mod_cast (show a < q by linarith)
          have prior := ih u less a gu
          have last : RationalCost.Walk (adjacency w) u v b := by
            simpa using RationalCost.Walk.cons ((edge_iff w u v b).mpr edge) (.nil v)
          simpa [eq] using walk_append prior last

theorem bellman_correct {w : Graph n} (hw : Positive w) {start : Fin n}
    {g : Labels n} (hg : Nonnegative g) (hb : Bellman w start g) (goal : Fin n) :
    DistanceResult w start goal (g goal) := by
  have zero : g start = 0 := by simpa using hb start
  cases value : g goal using WithTop.recTopCoe with
  | top =>
    intro t c walk isGoal
    have eq : t = goal := by simpa using isGoal
    subst t
    have bound := bellman_walk_le hw hg hb walk
    simp [value,zero] at bound
  | coe q =>
    refine ⟨goal,bellman_attains hw hb goal q value,by simp,?_⟩
    intro t c walk isGoal
    have eq : t = goal := by simpa using isGoal
    subst t
    have bound := bellman_walk_le hw hg hb walk
    simpa [value,zero] using bound

/-- The independent distance observation is unique, including infinity. -/
theorem distance_unique {w : Graph n} {start goal : Fin n} {a b : Cost}
    (ha : DistanceResult w start goal a) (hb : DistanceResult w start goal b) : a=b := by
  cases a using WithTop.recTopCoe with
  | top =>
    cases b using WithTop.recTopCoe with
    | top => rfl
    | coe b =>
      obtain ⟨v,walk,isGoal,_⟩ := hb
      exact False.elim (ha v b walk isGoal)
  | coe a =>
    cases b using WithTop.recTopCoe with
    | top =>
      obtain ⟨v,walk,isGoal,_⟩ := ha
      exact False.elim (hb v a walk isGoal)
    | coe b =>
      obtain ⟨u,pu,gu,amin⟩ := ha
      obtain ⟨v,pv,gv,bmin⟩ := hb
      exact congrArg (fun q : ℚ => (q : Cost)) (le_antisymm (amin v b pv gv) (bmin u a pu gu))

end Search.Incremental
