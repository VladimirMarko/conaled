import Examples.ConversionTrial.Scale
import Examples.ConversionTrial.Repair
import Examples.ConversionTrial.HeldOut
import Examples.ConversionTrial.Negative
import SquareKit.Internal.DependentFunctionConversion

/-! Private independent service-route oracle; direct task solutions are not imported. -/
set_option autoImplicit false
set_option warningAsError true
namespace Examples.ConversionTrial.ServiceReference
open SquareKit.Internal.DependentFunctions

theorem initial : Initial.Task := by
  refine ⟨?_, rfl, rfl⟩
  letI := Initial.lhs.decideEq Initial.rhs
  decide

theorem composition : Scale.CompositionTask := by
  intro r hr
  simp only [Scale.compositionSizes, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl <;>
    exact ⟨(Dep.convertible_iff _ _).mpr rfl, rfl⟩

theorem contexts : Scale.ContextTask := by
  intro k hk
  simp only [Scale.contextExtraBinders, List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl <;>
    exact ⟨(Dep.convertible_iff _ _).mpr rfl, rfl⟩

theorem substitutions : Scale.SubstitutionTask := by
  intro d hd
  simp only [Scale.substitutionSizes, List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl | rfl <;>
    exact ⟨(Dep.convertible_iff _ _).mpr rfl, rfl⟩

theorem before_repair : Repair.BeforeTask :=
  ⟨(Dep.convertible_iff _ _).mpr rfl, rfl⟩
theorem repair : Repair.Task := by
  refine ⟨(Dep.convertible_iff _ _).mpr rfl, rfl, ?_⟩
  intro h; cases h

theorem held_out : HeldOut.Task := ⟨(Dep.convertible_iff _ _).mpr rfl, rfl, rfl⟩
theorem head_negative : Negative.HeadTask := by
  refine ⟨rfl, ?_⟩
  intro h
  have he := FuncEq.normal_eq h
  cases he

theorem index_negative : Negative.IndexTask := by
  constructor
  · intro h; cases h
  · intro h; have ht := DepEq.type h; cases ht
end Examples.ConversionTrial.ServiceReference
