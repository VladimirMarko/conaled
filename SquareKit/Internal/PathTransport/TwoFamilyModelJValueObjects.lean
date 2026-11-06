import SquareKit.Internal.PathTransport.TwoFamilyModelJObjects
import SquareKit.Internal.PathTransport.TwoFamilyReindexedObjects
import SquareKit.Internal.PathTransport.TwoFamilySectionValues
namespace SquareKit.Internal.PathTransport.HigherInterpretation
open CategoryTheory Bicategory
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option backward.defeqAttrib.useBackward false
universe u
variable (C D : Context.{u}) {Γ : Context.{u}} (A : Family Γ)
 (x : ULift.{u+1} (TwoFamily.Section A.data))
variable (E : Family (((A.reindex (Δ := A.total) (TwoFamily.projectionHigher A.data)).identity
  (x.down.reindex A.data (TwoFamily.projectionHigher A.data)) (TwoFamily.variableSection A.data)).total))
local notation "M" => fullModel C D
def JValueFormula (d : (M).Section Γ ((M).subTy E ((M).toStructuralModel.rootSub A x)))
 (s : (M).Section ((M).toStructuralModel.pathContext A x) E) : Prop :=
 (rootContraction C D A x).val.ValueFormula E d.down s.down
theorem j_value_objects (d : (M).Section Γ ((M).subTy E ((M).toStructuralModel.rootSub A x))) :
 JValueFormula C D A x E d ((M).j A x .nil E d) :=
 j_objects C D A x E d.down
def JReindexedValueFormula
 (d : (M).Section Γ ((M).subTy E ((M).toStructuralModel.rootSub A x)))
 {Θ : Context.{u}} (σ : (M).Substitution Θ ((M).toStructuralModel.pathContext A x))
 (F : Family Θ) (s : (M).Section Θ F) : Prop :=
 (rootContraction C D A x).val.ReindexedValueFormula E d.down σ.down F s.down
theorem JValueFormula.reindex_cast
 (d : (M).Section Γ ((M).subTy E ((M).toStructuralModel.rootSub A x)))
 (s : (M).Section ((M).toStructuralModel.pathContext A x) E)
 (h : JValueFormula C D A x E d s)
 {Θ : Context.{u}} (σ : (M).Substitution Θ ((M).toStructuralModel.pathContext A x))
 (F : Family Θ) (e : (M).subTy E σ = F) :
 JReindexedValueFormula C D A x E d σ F
  (cast (congrArg ((M).Section Θ) e) ((M).subTm s σ)) := by
 have hc := sectionCast_down e ((M).subTm s σ)
 have r := @SourceContraction.ValueFormula.reindex_cast
  ((M).toStructuralModel.pathContext A x) Γ Θ ((M).toStructuralModel.rootSub A x).down
  (rootContraction C D A x).val E d.down s.down h σ.down F e
 exact (congrArg ((rootContraction C D A x).val.ReindexedValueFormula E d.down σ.down F) hc).mpr r
end SquareKit.Internal.PathTransport.HigherInterpretation

