import Applications.Search.Ordered.Exact

set_option autoImplicit false
set_option warningAsError true
namespace OrderedSearch

/-- First threshold index in a half-open interval, or its excluded upper endpoint. -/
def lowerBoundWith (pick : Nat → Nat) (hp : ∀ n, 0 < n → pick n < n)
    (f : Nat → Nat) (target lower : Nat) : Nat → Nat
  | 0 => lower
  | n + 1 =>
      let k := pick (n + 1)
      let m := lower + k
      if target ≤ f m then lowerBoundWith pick hp f target lower k
      else lowerBoundWith pick hp f target (m + 1) (n - k)
termination_by count => count
decreasing_by all_goals have _h := hp (n + 1) (by omega); omega

def ThresholdSpec (f : Nat → Nat) (target lower count result : Nat) : Prop :=
  lower ≤ result ∧ result ≤ lower + count ∧
    (∀ x, lower ≤ x → x < result → f x < target) ∧
    (∀ x, result ≤ x → x < lower + count → target ≤ f x)

theorem lowerBoundWith_spec (pick : Nat → Nat) (hp : ∀ n, 0 < n → pick n < n)
    (f : Nat → Nat) (hf : Monotone f) (target lower count : Nat) :
    ThresholdSpec f target lower count (lowerBoundWith pick hp f target lower count) := by
  cases count with
  | zero =>
    simp only [lowerBoundWith, ThresholdSpec, Nat.add_zero]
    exact ⟨Nat.le_refl _, Nat.le_refl _, fun _ h₁ h₂ => False.elim (by omega),
      fun _ h₁ h₂ => False.elim (by omega)⟩
  | succ n =>
    have hk := hp (n + 1) (by omega)
    rw [lowerBoundWith]
    split
    · rename_i hle
      have ih := lowerBoundWith_spec pick hp f hf target lower (pick (n + 1))
      rcases ih with ⟨hl, hu, hbefore, hafter⟩
      refine ⟨hl, by omega, hbefore, ?_⟩
      intro x hx hxu
      by_cases hm : x < lower + pick (n + 1)
      · exact hafter x hx hm
      · have := hf (a :=  lower + pick (n + 1)) (b := x) (by omega); omega
    · rename_i hle
      have ih := lowerBoundWith_spec pick hp f hf target
        (lower + pick (n + 1) + 1) (n - pick (n + 1))
      rcases ih with ⟨hl, hu, hbefore, hafter⟩
      refine ⟨by omega, by omega, ?_, ?_⟩
      · intro x hxl hx
        by_cases hm : lower + pick (n + 1) + 1 ≤ x
        · exact hbefore x hm hx
        · have := hf (a :=  x) (b := lower + pick (n + 1)) (by omega); omega
      · intro x hx hxu
        exact hafter x hx (by omega)
termination_by count
decreasing_by all_goals have _h := hp (n + 1) (by omega); omega

def lowerBound (f : Nat → Nat) (target lower count : Nat) : Nat :=
  lowerBoundWith upperPick upperPick_lt f target lower count

theorem lowerBound_spec (f : Nat → Nat) (hf : Monotone f) (target lower count : Nat) :
    ThresholdSpec f target lower count (lowerBound f target lower count) :=
  lowerBoundWith_spec upperPick upperPick_lt f hf target lower count

end OrderedSearch
