import SquareKit.SmoothQuotientLocalSections
import SquareKit.SmoothQuotientGeneratedDescentEquivalence
import SquareKit.SmoothQuotientGeneratedComposition
import SquareKit.Internal.PathTransport.AlignedSignatureComparison

/-! The actual descent/restriction square acts coherently on generated contexts
and dependent families, with the original direct interpretations. -/
noncomputable section
namespace SquareKit.SmoothQuotientGeneratedBaseChange
open CategoryTheory CategoryTheory.Functor SheafActionQuotient SmoothOpenSite
open SmoothQuotientDeformations Internal.PathTransport GroupoidModel Comparison
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {H : Type} [Group H] {M X Y : Sheaf topology Type}
variable (a : Action (locallyConstantGroup H) M) (A : SplitSheaf.Ty X)
variable [Presheaf.IsLocallySurjective topology (SplitSheaf.p A).hom]
local instance : Groupoid (Descent.Datum (a := a) A) := Groupoid.ofIsGroupoid
local instance (f : Y ⟶ X) : Groupoid (Descent.Datum (a := a) (SplitSheaf.tySub A f)) :=
  Groupoid.ofIsGroupoid
variable (f : Y ⟶ X)

def leftFiberMap : CocycleDatum.fiberFamily (a := a) (A := A) ⟶
    (Descent.descentFunctor a A ⋙ restriction f) ⋙ family a Y :=
  (CocycleDatum.fiberComparison (a := a) (A := A)).inv ≫
    whiskerLeft (Descent.descentFunctor a A) (restrictionFamily f)

def rightFiberMap : CocycleDatum.fiberFamily (a := a) (A := A) ⟶
    (Descent.baseChange f ⋙ Descent.descentFunctor a (SplitSheaf.tySub A f)) ⋙ family a Y :=
  CocycleDatum.fiberBaseChange (a := a) (A := A) f ≫
    whiskerLeft (Descent.baseChange f)
      (CocycleDatum.fiberComparison (a := a) (A := SplitSheaf.tySub A f)).inv

/-- Orient the existing deformation square using its actual fiber isomorphisms.
No generated compatibility premise is introduced. -/
theorem primitive_square :
    leftFiberMap a A f ≫
        whiskerRight (Descent.baseChangeComparison f).hom (family a Y) =
      rightFiberMap a A f := by
  have hh := congrArg (fun k =>
      (CocycleDatum.fiberComparison (a := a) (A := A)).inv ≫ k ≫
        whiskerLeft (Descent.baseChange f)
          (CocycleDatum.fiberComparison (a := a) (A := SplitSheaf.tySub A f)).inv)
    (CocycleDatum.fiberBaseChange_square (a := a) (A := A) f)
  simp [Category.assoc, ← whiskerLeft_comp] at hh
  apply NatTrans.ext
  funext d
  apply ConcreteCategory.hom_ext
  intro v
  exact congrArg (fun k : CocycleDatum.fiberFamily (a := a) (A := A) ⟶
    (Descent.baseChange f ⋙ Descent.descentFunctor a (SplitSheaf.tySub A f)) ⋙ family a Y =>
      k.app d v) hh

def leftSignature : Comparison.Signature.{1} := alignedUniverseSignature
  (Descent.descentFunctor a A ⋙ restriction f)
  (CocycleDatum.fiberFamily (a := a) (A := A)) (family a Y) (leftFiberMap a A f)

def rightSignature : Comparison.Signature.{1} := alignedUniverseSignature
  (C := Descent.Datum (a := a) A) (D := Object a Y)
  (Descent.baseChange f ⋙ Descent.descentFunctor a (SplitSheaf.tySub A f))
  (CocycleDatum.fiberFamily (a := a) (A := A)) (family a Y) (rightFiberMap a A f)

def contextComparison (hΓ : Typed.CtxDeriv.{2} Γ γ) :
    generatedContextMap (leftSignature a A f) hΓ ≅
      generatedContextMap (rightSignature a A f) hΓ :=
  alignedContextComparison (Descent.baseChangeComparison (a := a) (A := A) f)
    (CocycleDatum.fiberFamily (a := a) (A := A)) (family a Y)
    (leftFiberMap a A f) (rightFiberMap a A f)
    (primitive_square a A f) hΓ

def familyComparison (hΓ : Typed.CtxDeriv.{2} Γ γ) (hB : Typed.TyDeriv.{2} Γ γ B b) :
    Modification (contextComparison a A f hΓ)
      (generatedFamilyMap (leftSignature a A f) hΓ hB)
      (generatedFamilyMap (rightSignature a A f) hΓ hB) :=
  alignedFamilyComparison (Descent.baseChangeComparison (a := a) (A := A) f)
    (CocycleDatum.fiberFamily (a := a) (A := A)) (family a Y)
    (leftFiberMap a A f) (rightFiberMap a A f)
    (primitive_square a A f) hΓ hB

end SquareKit.SmoothQuotientGeneratedBaseChange
