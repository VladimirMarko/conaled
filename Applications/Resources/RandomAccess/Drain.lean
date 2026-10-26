import Applications.Resources.RandomAccess.End

/-! Finite end-operation accounting from checkpoint 233.
Provenance, source domains and statement review:
`docs/research/adwh-random-access-end-costs.md`. -/
set_option autoImplicit false
set_option warningAsError true

namespace Resources.RandomAccessCosts
open RandomAccess
universe u
variable {α : Type u}

/-- Up to n successful removals; a failed empty removal is charged and stops. -/
def drainRun : Nat → RAList α → (List α × RAList α) × Nat
  | 0, ds => (([], ds), 0)
  | n + 1, ds =>
      let next := unconsRARun ds
      match next.1 with
      | none => (([], ds), next.2)
      | some (x, ys) =>
          let rest := drainRun n ys
          ((x :: rest.1.1, rest.1.2), next.2 + rest.2)

theorem drainRun_spec (n : Nat) {ds : RAList α} (h : Inv ds) :
    Inv (drainRun n ds).1.2 ∧
      (drainRun n ds).1.1 = (fromRA ds).take n ∧
      fromRA (drainRun n ds).1.2 = (fromRA ds).drop n ∧
      (drainRun n ds).2 + zeros (drainRun n ds).1.2 ≤ zeros ds + 2 * n := by
  induction n generalizing ds with
  | zero => simp [drainRun, h]
  | succ n ih =>
    by_cases he : ds = []
    · subst ds
      simp [drainRun, unconsRARun_exact, unconsRA, unconsT, borrowCost, zeros,
        fromRA, RandomAccess.Inv, Valid.nil]
      omega
    · obtain ⟨x, ys, hu, hy, ha, hc⟩ := unconsRA_spec h he
      have hr := ih hy
      have hp := unconsRA_potential h hu
      rw [unconsRARun_exact] at hp
      simp only [drainRun, unconsRARun_exact, hu]
      rw [ha]
      simp only [List.take_succ_cons, List.drop_succ_cons]
      refine ⟨hr.1, congrArg (x :: ·) hr.2.1, hr.2.2.1, ?_⟩
      omega

theorem drainRun_cost_lower (n : Nat) (ds : RAList α) :
    (drainRun n ds).1.1.length ≤ (drainRun n ds).2 := by
  induction n generalizing ds with
  | zero => simp [drainRun]
  | succ n ih =>
    have hp := (borrowCost_bounds ds).1
    cases he : unconsRA ds with
    | none => simp [drainRun, unconsRARun_exact, he]
    | some p =>
      obtain ⟨x, ys⟩ := p
      have hr := ih ys
      simp only [drainRun, unconsRARun_exact, he, List.length_cons]
      omega

theorem zeros_le_elements {ds : RAList α} (h : Inv ds) :
    zeros ds ≤ (fromRA ds).length := by
  by_cases he : ds = []
  · simp [he, zeros, fromRA]
  · have hn : (fromRA ds).length ≠ 0 := by
      intro hz
      exact fromRA_ne_nil h he (List.length_eq_zero_iff.mp hz)
    have hl : (fromRA ds).length.log2 < (fromRA ds).length :=
      (Nat.log2_lt hn).mpr Nat.lt_two_pow_self
    have hd := digits_log_bound h
    have hz := ones_add_zeros ds
    omega

theorem full_drain_value {ds : RAList α} (h : Inv ds) :
    (drainRun (fromRA ds).length ds).1 = (fromRA ds, []) := by
  have hs := drainRun_spec (fromRA ds).length h
  have ha : (drainRun (fromRA ds).length ds).1.1 = fromRA ds := by
    simpa using hs.2.1
  have hb : (drainRun (fromRA ds).length ds).1.2 = [] := by
    apply valid_abstraction_injective hs.1 (Valid.nil 0)
    simpa [fromRA] using hs.2.2.1
  exact Prod.ext ha hb

theorem full_drain_linear_bounds {ds : RAList α} (h : Inv ds) :
    (fromRA ds).length ≤ (drainRun (fromRA ds).length ds).2 ∧
      (drainRun (fromRA ds).length ds).2 ≤ 3 * (fromRA ds).length := by
  have hs := drainRun_spec (fromRA ds).length h
  have hl := drainRun_cost_lower (fromRA ds).length ds
  rw [full_drain_value h] at hl
  have hz := zeros_le_elements h
  exact ⟨hl, by omega⟩

def headRARun (ds : RAList α) : Option α × Nat :=
  let next := unconsRARun ds
  (next.1.map Prod.fst, next.2)

def tailRARun (ds : RAList α) : Option (RAList α) × Nat :=
  let next := unconsRARun ds
  (next.1.map Prod.snd, next.2)

theorem headRARun_value (ds : RAList α) : (headRARun ds).1 = headRA ds := by
  simp only [headRARun, unconsRARun_exact, headRA]

theorem tailRARun_value (ds : RAList α) : (tailRARun ds).1 = tailRA ds := by
  simp only [tailRARun, unconsRARun_exact, tailRA]

theorem head_tail_log_bounds {ds : RAList α} (h : Inv ds) :
    (headRARun ds).2 ≤ (fromRA ds).length.log2 + 2 ∧
      (tailRARun ds).2 ≤ (fromRA ds).length.log2 + 2 :=
  ⟨unconsRARun_log_bound h, unconsRARun_log_bound h⟩

end Resources.RandomAccessCosts
