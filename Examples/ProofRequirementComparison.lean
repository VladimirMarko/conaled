import Examples.ProofRequirementManual
import Examples.ProofRequirementAssisted

/-! Coordinator comparisons after both #293 author attempts closed. -/
namespace ProofRequirementTrial.Comparison

universe u v

/-- Both E interfaces express the same binary reversal law. -/
theorem reversal_requirements_iff {A : Type u} (m : A → A → A) (f : A → A) :
    Manual.ReversalRequirements m f ↔ Assisted.ReversesOperation m f :=
  ⟨fun h => h.reverse_op, fun h => ⟨h⟩⟩

/-- The assisted author's law supplies the manual author's observation law. -/
theorem observed_of_carrier {A : Type u} {B : Type v}
    {m : A → A → A} {e : A} (observe : A → B) (h : Assisted.RightUnit m e) :
    Manual.ObservedRightUnit m e observe :=
  Manual.observedRightUnit_of_rightUnit observe h

/-- Under the carrier law, both authors retain the same full subtype data. -/
theorem selections_equal {A : Type u} {B : Type v} {m : A → A → A} {e : A}
    (observe : A → B) (h : Assisted.RightUnit m e) (x : A) :
    Manual.selected (observed_of_carrier observe h) x =
      Assisted.select m e observe h x := rfl

/-- A constant observation satisfies the observation law despite adding one. -/
theorem constant_observed_unit :
    Manual.ObservedRightUnit Nat.add 1 (fun _ : Nat => ()) := fun _ => rfl

theorem constant_selection :
    (Manual.selected constant_observed_unit 0).val = 0 :=
  Manual.selected_value constant_observed_unit 0

/-- This actual model separates the sufficient law choices; it is not a minimality claim. -/
theorem observed_does_not_imply_carrier :
    ¬ (Manual.ObservedRightUnit Nat.add 1 (fun _ : Nat => ()) →
      Assisted.RightUnit Nat.add 1) := by
  intro implication
  exact Assisted.nat_rightUnit_missing (implication constant_observed_unit)

end ProofRequirementTrial.Comparison
