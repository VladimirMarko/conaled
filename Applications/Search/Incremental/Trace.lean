import Applications.Search.Incremental.Keys
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! Finite legal expansion traces, without a termination premise or numeric
well-foundedness assumption on rational labels. -/
set_option autoImplicit false
set_option warningAsError true
namespace Search.Incremental
variable {n : Nat}

/-- A consistent vertex below the entire inconsistent frontier. -/
def Frozen (w : Graph n) (start : Fin n) (h : Fin n → ℚ) (g : Labels n) (v : Fin n) : Prop :=
  g v = rhsValue w start g v ∧
    ∀ u, g u ≠ rhsValue w start g u → key w start h g v ≤ key w start h g u

theorem frozen_step (w : Graph n) (hw : Positive w) (start : Fin n)
    (h : Fin n → ℚ) (hh : ∀ u v, (h u : Cost) ≤ w u v + (h v : Cost))
    (g : Labels n) (u v : Fin n) (hu : Selected w start h g u) (hv : Frozen w start h g v) :
    Frozen w start h (nextLabels w start g u) v ∧ nextLabels w start g u v = g v := by
  have hne : v ≠ u := by intro he; subst v; exact hu.1 hv.1
  have he := nextLabels_of_ne w start g u v hne
  have hc : nextLabels w start g u v = rhsValue w start (nextLabels w start g u) v := by
    by_contra hn
    have hp := newly_inconsistent_key w hw start h hh g u v hu hv.1 hn
    have hb : key w start h (nextLabels w start g u) v ≤ key w start h g v := by
      change priority (min (nextLabels w start g u v)
        (rhsValue w start (nextLabels w start g u) v)) (h v) ≤
        priority (min (g v) (rhsValue w start g v)) (h v)
      rw [he, ← hv.1, min_self]
      exact priority_mono (min_le_left _ _) _
    exact not_lt_of_ge (hb.trans (hv.2 u hu.1)) hp
  have hk : key w start h (nextLabels w start g u) v = key w start h g v := by
    unfold key labelKey
    rw [← hc, ← hv.1, he]
  refine ⟨⟨hc, ?_⟩, he⟩
  intro z hz
  rw [hk]
  exact (hv.2 u hu.1).trans (next_inconsistent_key w hw start h hh g u z hu hz)

theorem overconsistent_frozen (w : Graph n) (hw : Positive w) (start : Fin n)
    (h : Fin n → ℚ) (hh : ∀ u v, (h u : Cost) ≤ w u v + (h v : Cost))
    (g : Labels n) (u : Fin n) (hu : Selected w start h g u)
    (ho : rhsValue w start g u < g u) : Frozen w start h (nextLabels w start g u) u := by
  have hc : nextLabels w start g u u = rhsValue w start (nextLabels w start g u) u := by
    simp only [nextLabels, ite_eq_left ho, Function.update_self]
    exact (overconsistent_rhs w hw start g u ho).symm
  have hk : key w start h (nextLabels w start g u) u = key w start h g u := by
    simpa only [nextLabels, ite_eq_left ho] using overconsistent_key w hw start h g u ho
  refine ⟨hc, fun v hv => ?_⟩
  rw [hk]
  exact next_inconsistent_key w hw start h hh g u v hu hv

inductive Trace (w : Graph n) (start : Fin n) (h : Fin n → ℚ) :
    Labels n → List (Fin n) → Labels n → Prop where
  | nil (g : Labels n) : Trace w start h g [] g
  | cons {g out : Labels n} {u : Fin n} {us : List (Fin n)} :
      Selected w start h g u → Trace w start h (nextLabels w start g u) us out →
        Trace w start h g (u :: us) out

theorem Trace.frozen (w : Graph n) (hw : Positive w) (start : Fin n)
    (h : Fin n → ℚ) (hh : ∀ u v, (h u : Cost) ≤ w u v + (h v : Cost))
    {g out : Labels n} {us : List (Fin n)} (tr : Trace w start h g us out)
    (v : Fin n) (hv : Frozen w start h g v) :
    Frozen w start h out v ∧ out v = g v ∧ v ∉ us := by
  induction tr with
  | nil => exact ⟨hv, rfl, by simp⟩
  | @cons g out u us hu ht ih =>
    obtain ⟨hf, he⟩ := frozen_step w hw start h hh g u v hu hv
    obtain ⟨hf', he', hn⟩ := ih hf
    have hne : v ≠ u := by intro he; subst v; exact hu.1 hv.1
    exact ⟨hf', he'.trans he, by simp [hne, hn]⟩

theorem Trace.count_le_one_of_top (w : Graph n) (hw : Positive w) (start : Fin n)
    (h : Fin n → ℚ) (hh : ∀ u v, (h u : Cost) ≤ w u v + (h v : Cost))
    {g out : Labels n} {us : List (Fin n)} (tr : Trace w start h g us out)
    (v : Fin n) (hv : g v = ⊤) : us.count v ≤ 1 := by
  induction tr with
  | nil => simp
  | @cons g out u us hu ht ih =>
    by_cases he : v = u
    · subst v
      have ho : rhsValue w start g u < g u := by
        rw [hv]
        exact lt_top_iff_ne_top.mpr (by simpa [hv, eq_comm] using hu.1)
      have hf := overconsistent_frozen w hw start h hh g u hu ho
      have hn := (ht.frozen w hw start h hh u hf).2.2
      simp [List.count_eq_zero.mpr hn]
    · have hv' : nextLabels w start g u v = ⊤ := (nextLabels_of_ne w start g u v he).trans hv
      simpa [he, Ne.symm he] using ih hv'

theorem Trace.count_le_two (w : Graph n) (hw : Positive w) (start : Fin n)
    (h : Fin n → ℚ) (hh : ∀ u v, (h u : Cost) ≤ w u v + (h v : Cost))
    {g out : Labels n} {us : List (Fin n)} (tr : Trace w start h g us out)
    (v : Fin n) : us.count v ≤ 2 := by
  induction tr with
  | nil => simp
  | @cons g out u us hu ht ih =>
    by_cases he : v = u
    · subst v
      by_cases ho : rhsValue w start g u < g u
      · have hf := overconsistent_frozen w hw start h hh g u hu ho
        have hn := (ht.frozen w hw start h hh u hf).2.2
        simp [List.count_eq_zero.mpr hn]
      · have hv : nextLabels w start g u u = ⊤ := by simp [nextLabels, ho]
        have hb := ht.count_le_one_of_top w hw start h hh u hv
        simp only [List.count_cons_self]
        omega
    · simpa [he, Ne.symm he] using ih

theorem sum_counts (us : List (Fin n)) : (∑ v : Fin n, us.count v) = us.length := by
  induction us with
  | nil => simp
  | cons u us ih =>
    have hs : (∑ x : Fin n, if u = x then 1 else 0) = 1 := by
      rw [Finset.sum_eq_single u]
      · simp
      · intro b _ hb; simp [Ne.symm hb]
      · simp
    simpa [List.count_cons, Finset.sum_add_distrib, ih] using hs

/-- The source bound counts expansions within one frozen graph, not primitive work. -/
theorem Trace.length_le (w : Graph n) (hw : Positive w) (start : Fin n)
    (h : Fin n → ℚ) (hh : ∀ u v, (h u : Cost) ≤ w u v + (h v : Cost))
    {g out : Labels n} {us : List (Fin n)} (tr : Trace w start h g us out) : us.length ≤ 2*n := by
  rw [← sum_counts]
  calc
    (∑ v : Fin n, us.count v) ≤ ∑ _v : Fin n, 2 :=
      Finset.sum_le_sum fun v _ => tr.count_le_two w hw start h hh v
    _ = 2*n := by simp [Nat.mul_comm]

end Search.Incremental
