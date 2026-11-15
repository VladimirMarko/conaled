import Mathlib.Order.Nucleus

/-! A two-query Heyting-algebra specialization of the least oracle-modality construction.
The finite closure is proved from return/ask rules, separately from the nucleus universal property. -/

namespace OracleModality

variable {H : Type*} [HeytingAlgebra H]

/-- The open nucleus associated with one persistent proposition. -/
def openNucleus (p : H) : Nucleus H where
  toFun s := p ⇨ s
  map_inf' := himp_inf_distrib p
  idempotent' s := by simp only [himp_idem]; exact le_rfl
  le_apply' _ := le_himp

@[simp] theorem open_apply (p s : H) : openNucleus p s = p ⇨ s := rfl

/-- One layer of return or either of the two possible queries. -/
def step (p q s t : H) : H := s ⊔ (p ⇨ t) ⊔ (q ⇨ t)

/-- Candidate closure, independently specified by a Heyting implication. -/
def oracle (p q s : H) : H := (p ⊓ q) ⇨ s

theorem return_le (p q s : H) : s ≤ oracle p q s := le_himp

theorem step_mono (p q s : H) : Monotone (step p q s) := by
  intro a b h
  exact sup_le_sup (sup_le_sup_left (himp_le_himp_left h) _) (himp_le_himp_left h)

theorem ask_left (p q s : H) : p ⇨ oracle p q s = oracle p q s := by
  simp only [oracle, himp_himp, inf_left_idem]

theorem ask_right (p q s : H) : q ⇨ oracle p q s = oracle p q s := by
  simp only [oracle, himp_himp]
  congr 1
  exact inf_left_comm q p q |>.trans (by rw [inf_idem])

theorem step_fixed (p q s : H) : step p q s (oracle p q s) = oracle p q s := by
  rw [step, ask_left, ask_right, sup_eq_right.mpr (return_le p q s), sup_idem]

/-- The independently specified result is reached after two actual query layers. -/
theorem two_steps (p q s : H) : step p q s (step p q s s) = oracle p q s := by
  apply le_antisymm
  · calc
      step p q s (step p q s s) ≤ step p q s (step p q s (oracle p q s)) :=
        step_mono p q s (step_mono p q s (return_le p q s))
      _ = oracle p q s := by rw [step_fixed, step_fixed]
  · calc
      oracle p q s = p ⇨ q ⇨ s := (himp_himp p q s).symm
      _ ≤ p ⇨ step p q s s := himp_le_himp_left le_sup_right
      _ ≤ step p q s (step p q s s) := le_sup_of_le_left le_sup_right

/-- Least closure under return and both queries, not a stored correctness assumption. -/
theorem least_prefixed {p q s r : H} (hs : s ≤ r)
    (hp : p ⇨ r ≤ r) (hq : q ⇨ r ≤ r) : oracle p q s ≤ r := by
  have hr : step p q s r ≤ r := sup_le (sup_le hs hp) hq
  rw [← two_steps]
  exact (step_mono p q s ((step_mono p q s hs).trans hr)).trans hr

theorem open_comp (p q s : H) : openNucleus p (openNucleus q s) = openNucleus (p ⊓ q) s :=
  himp_himp p q s

theorem open_commute (p q s : H) : openNucleus p (openNucleus q s) =
    openNucleus q (openNucleus p s) := himp_left_comm p q s

/-- A nucleus forces p precisely when it lies above the one-query construction. -/
theorem open_le_iff (p : H) (j : Nucleus H) : openNucleus p ≤ j ↔ j p = ⊤ := by
  constructor
  · intro h
    apply top_le_iff.mp
    simpa using h p
  · intro hp s
    calc
      p ⇨ s ≤ j (p ⇨ s) := j.le_apply
      _ = j (p ⇨ s) ⊓ j p := by rw [hp, inf_top_eq]
      _ = j ((p ⇨ s) ⊓ p) := j.map_inf.symm
      _ ≤ j s := j.monotone himp_inf_le

/-- Bounded Proposition 6: this is the least nucleus forcing the two given answers. -/
theorem least_forcing (p q : H) (j : Nucleus H) :
    openNucleus (p ⊓ q) ≤ j ↔ j p = ⊤ ∧ j q = ⊤ := by
  rw [open_le_iff, j.map_inf, inf_eq_top_iff]

/-- The join is also the proved composition here; arbitrary nuclei need not compose this way. -/
theorem join_characterization (p q : H) (j : Nucleus H) :
    openNucleus (p ⊓ q) ≤ j ↔ openNucleus p ≤ j ∧ openNucleus q ≤ j := by
  rw [least_forcing, open_le_iff, open_le_iff]

end OracleModality
