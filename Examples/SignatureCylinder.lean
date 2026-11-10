import SquareKit.Internal.PathTransport.GeneratedCylinderTerms
import SquareKit.Internal.PathTransport.GeneratedCylinderContraction
import Examples.SignatureInterpretationMaps
import SquareKit.Internal.PathTransport.SelectedLiftIso
import Mathlib.CategoryTheory.CodiscreteCategory

/-! A selected cylinder comparison for unequal base functors and a
noninjective primitive fiber map. -/
noncomputable section
namespace Examples.SignatureCylinder
open CategoryTheory SquareKit.Internal.PathTransport
open GroupoidModel Comparison Typed

local instance : Groupoid (Codiscrete Bool) where
  toCategory := inferInstance
  inv _ := ()
  inv_comp _ := rfl
  comp_inv _ := rfl

local instance : Groupoid (Discrete PUnit.{1}) := Groupoid.ofIsGroupoid

abbrev C := Grpd.of (Discrete PUnit.{1})
abbrev D := Grpd.of (Codiscrete Bool)
def left : C ⥤ D := Codiscrete.functor (fun _ => false)
def right : C ⥤ D := Codiscrete.functor (fun _ => true)
def comparison : left ≅ right := Codiscrete.natIso

def before : C ⥤ Type := (CategoryTheory.Functor.const _).obj Bool
def after : D ⥤ Type := (CategoryTheory.Functor.const _).obj PUnit

def alpha : before ⟶ left ⋙ after where
  app _ := ↾fun _ => PUnit.unit
  naturality {_ _} _ := rfl

def beta : before ⟶ right ⋙ after where
  app _ := ↾fun _ => PUnit.unit
  naturality {_ _} _ := rfl

theorem unequal : left ≠ right := by
  intro h
  have he := congrArg (fun F => (F.obj (Discrete.mk PUnit.unit)).as) h
  cases he

theorem noninjective : ¬ Function.Injective (alpha.app (Discrete.mk PUnit.unit)) := by
  intro h
  have he := h (a₁ := false) (a₂ := true) rfl
  cases he

def context : CtxDeriv [.base] (extendCode emptyCode.{1} (baseCode emptyCode)) :=
  .ext .empty (.base .empty)

/-- The public generated result is applicable despite both separating cases. -/
def generated := Comparison.SignatureCylinder.contextComparison left before comparison
  after alpha beta rfl context

/-- Evaluation retains the chosen base component, rather than choosing a new
arrow after discarding it in the projection. -/
example : (Comparison.SignatureCylinder.evaluation left).map
    ((Comparison.SignatureCylinder.endpointIso left comparison).hom.app (Discrete.mk PUnit.unit)) =
      comparison.hom.app (Discrete.mk PUnit.unit) :=
  Comparison.SignatureCylinder.endpointIso_evaluation left comparison _

/-- The chosen comparison respects the selected counit for a two-binder
root/tail contraction whose second binder depends on the first. -/
def dependentCounit := Comparison.SignatureCylinder.contextComparison_rootTail_counit
  left before comparison after alpha beta rfl
  SignatureInterpretationMaps.DependentTail.context
  (.base SignatureInterpretationMaps.DependentTail.context)
  SignatureInterpretationMaps.DependentTail.point.deriv
  SignatureInterpretationMaps.DependentTail.tail

/-- The actual generic contextual-J section commutes with the selected
comparison; the term is produced by the existing path-command authoring API. -/
def dependentJ := Comparison.SignatureCylinder.contextComparison_section
  left before comparison after alpha beta rfl
  SignatureInterpretationMaps.DependentTail.withFiber
  SignatureInterpretationMaps.DependentTail.command.motive.typing
  SignatureInterpretationMaps.DependentTail.generic

end Examples.SignatureCylinder
