import Examples.ConversionTrial.Scale
import SquareKit.Internal.DependentFunctionConversion

set_option autoImplicit false
set_option warningAsError true

namespace Examples.ConversionTrial.Scale
open SquareKit.Internal.DependentFunctions

theorem composition_solved : CompositionTask := by
  intro r h
  simp only [compositionSizes, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl
  all_goals
    refine ⟨(Dep.convertible_iff _ _).mpr ?_, ?_⟩ <;> rfl

theorem context_solved : ContextTask := by
  intro k h
  simp only [contextExtraBinders, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl
  all_goals
    refine ⟨(Dep.convertible_iff _ _).mpr ?_, ?_⟩ <;> rfl

theorem substitution_solved : SubstitutionTask := by
  intro d h
  simp only [substitutionSizes, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl
  all_goals
    refine ⟨(Dep.convertible_iff _ _).mpr ?_, ?_⟩ <;> rfl

end Examples.ConversionTrial.Scale
