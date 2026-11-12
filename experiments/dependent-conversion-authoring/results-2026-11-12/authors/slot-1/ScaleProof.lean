import Examples.ConversionTrial.Scale
import SquareKit.Internal.DependentFunctionConversion

set_option autoImplicit false
set_option warningAsError true

namespace Examples.ConversionTrial.Scale
open SquareKit.Internal.DependentFunctions

theorem composition_proved : CompositionTask := by
  intro r hr
  simp [compositionSizes] at hr
  rcases hr with rfl | rfl | rfl
  all_goals exact ⟨(Dep.convertible_iff _ _).mpr rfl, rfl⟩

theorem context_proved : ContextTask := by
  intro k hk
  simp [contextExtraBinders] at hk
  rcases hk with rfl | rfl | rfl
  all_goals exact ⟨(Dep.convertible_iff _ _).mpr rfl, rfl⟩

theorem substitution_proved : SubstitutionTask := by
  intro d hd
  simp [substitutionSizes] at hd
  rcases hd with rfl | rfl | rfl
  all_goals exact ⟨(Dep.convertible_iff _ _).mpr rfl, rfl⟩

end Examples.ConversionTrial.Scale
