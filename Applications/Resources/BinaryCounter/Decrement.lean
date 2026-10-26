import Applications.Resources.BinaryCounter

/-! Finite end-operation accounting from checkpoint 233.
Provenance, source domains and statement review:
`docs/research/adwh-random-access-end-costs.md`. -/
set_option autoImplicit false
set_option warningAsError true

namespace Resources.BinaryCounter

def decBits : Bits → Option Bits
  | [] => none
  | true :: bs => some (if bs.isEmpty then [] else false :: bs)
  | false :: bs => (decBits bs).map (true :: ·)

theorem decBits_spec {bs : Bits} (h : Canonical bs) (hne : bs ≠ []) :
    ∃ ys, decBits bs = some ys ∧ Canonical ys ∧
      value bs = value ys + 1 := by
  induction bs with
  | nil => exact False.elim (hne rfl)
  | cons b bs ih =>
    cases b with
    | true =>
      cases bs with
      | nil => exact ⟨[], rfl, True.intro, rfl⟩
      | cons c cs =>
        refine ⟨false :: c :: cs, rfl, ?_, ?_⟩
        · simpa [Canonical] using h
        · simp [value]
          omega
    | false =>
      have hb : bs ≠ [] := by intro he; simp [he, Canonical] at h
      have hc : Canonical bs := by simpa [Canonical, hb] using h
      obtain ⟨ys, he, hy, hv⟩ := ih hc hb
      refine ⟨true :: ys, ?_, ?_, ?_⟩
      · simp [decBits, he]
      · by_cases hz : ys = []
        · simp [hz, Canonical]
        · simpa [Canonical, hz] using hy
      · simp only [value]
        omega

end Resources.BinaryCounter
