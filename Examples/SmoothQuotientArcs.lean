import SquareKit.SmoothQuotientArcs
import SquareKit.SmoothDiscreteMapping

/-! Pointed quotient arcs over arbitrary sheaf parameters, including the
zero inclusion as a parameter change and ineffective scalar actions. -/
noncomputable section
namespace Examples.SmoothQuotientArcs
open CategoryTheory Opposite SquareKit SheafRelation SheafFunction
open SmoothOpenSite SheafActionQuotient
local notation "D" => PresentationGeometry.infinitesimal topology
local notation "R" => PresentationGeometry.scalar topology
variable {H : Type} [Group H] {M : Sheaf topology Type}
variable (a : Action (locallyConstantGroup H) M)

/-- The inverse comparison recovers arbitrary pointed objects, including
their chosen boundary isomorphisms. -/
example (X : Sheaf topology Type) (P : SquareKit.SmoothQuotientArcs.Pointed a X) :
    (SquareKit.SmoothQuotientArcs.comparison a X).functor.obj
      ((SquareKit.SmoothQuotientArcs.comparison a X).inverse.obj P) ≅ P :=
  (SquareKit.SmoothQuotientArcs.comparison a X).counitIso.app P

/-- Restriction along zero acts on the entire pointed datum. This parameter
map changes D×X to X, rather than testing only an identity restriction. -/
example (X : Sheaf topology Type) (h : product D X ⟶ exponential D M) :
    (SquareKit.SmoothQuotientArcs.comparison a X).functor.obj
      ⟨parameterZero X ≫ h⟩ =
    (SquareKit.SmoothQuotientArcs.baseChange a (parameterZero X)).obj
      ((SquareKit.SmoothQuotientArcs.comparison a (product D X)).functor.obj ⟨h⟩) :=
  congrArg (fun F => F.obj (Discrete.mk h))
    (SquareKit.SmoothQuotientArcs.comparison_natural a (parameterZero X))

example (X : Sheaf topology Type) (h : X ⟶ exponential D M) :
    ((SquareKit.SmoothQuotientArcs.comparison a X).functor.obj ⟨h⟩).hom =
      𝟙 (chart a (parameterZero X ≫ uncurry h)) :=
  SquareKit.SmoothQuotientArcs.comparison_boundary a X h

/-- The homotopy-pullback comparison also applies when every label acts
trivially on the scalar sheaf. -/
def ineffectiveScalar : Action (locallyConstantGroup H) R where
  act _ _ x := x
  one_act _ _ := rfl
  mul_act _ _ _ _ := rfl
  natural _ _ _ := rfl

example (X : Sheaf topology Type) (b v : X ⟶ R) :
    ((SquareKit.SmoothQuotientArcs.comparison (ineffectiveScalar (H := H)) X).functor.obj
      ⟨curry (SmoothGeometricKL.rebuild (lift b v))⟩).left.as = b := by
  change parameterZero X ≫ uncurry (curry (SmoothGeometricKL.rebuild (lift b v))) = b
  rw [beta, SmoothDiscreteMapping.zero_rebuild]
  rfl

example (X : Sheaf topology Type) (b v : X ⟶ R) :
    ((SquareKit.SmoothQuotientArcs.comparison (ineffectiveScalar (H := H)) X).functor.obj
      ⟨curry (SmoothGeometricKL.rebuild (lift b v))⟩).right =
      chart ineffectiveScalar (SmoothGeometricKL.rebuild (lift b v)) := by
  change chart ineffectiveScalar (uncurry (curry _)) = _
  rw [beta]

end Examples.SmoothQuotientArcs
