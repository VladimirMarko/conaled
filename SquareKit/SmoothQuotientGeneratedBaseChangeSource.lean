import SquareKit.SmoothQuotientGeneratedBaseChange
import SquareKit.Internal.PathTransport.UniversalTransferComparison

/-! Composed actual smooth signatures and the unchanged source proof. -/
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

def baseChangeSignature : Comparison.Signature.{1} := alignedUniverseSignature
  (Descent.baseChange (a := a) (A := A) f)
  (CocycleDatum.fiberFamily (a := a) (A := A))
  (CocycleDatum.fiberFamily (a := a) (A := SplitSheaf.tySub A f))
  (CocycleDatum.fiberBaseChange f)

theorem leftSignature_composed : leftSignature a A f =
    (SmoothQuotientGeneratedDescent.signature a A).horizontal
      (SmoothQuotientComparison.signature (a := a) f) rfl HEq.rfl := rfl

theorem rightSignature_composed : rightSignature a A f =
    (baseChangeSignature a A f).horizontal
      (SmoothQuotientGeneratedDescent.signature a (SplitSheaf.tySub A f)) rfl HEq.rfl := rfl

def SectionCoherence (hΓ : Typed.CtxDeriv.{2} Γ γ)
    (hB : Typed.TyDeriv.{2} Γ γ B b) (hx : Typed.TmDeriv.{2} Γ γ B b t x) : Prop :=
  AlignedSectionCoherence (Descent.baseChangeComparison (a := a) (A := A) f)
    (CocycleDatum.fiberFamily (a := a) (A := A)) (family a Y)
    (leftFiberMap a A f) (rightFiberMap a A f) (primitive_square a A f) hΓ hB hx

theorem sectionCoherence (hΓ : Typed.CtxDeriv.{2} Γ γ)
    (hB : Typed.TyDeriv.{2} Γ γ B b) (hx : Typed.TmDeriv.{2} Γ γ B b t x) :
    SectionCoherence a A f hΓ hB hx :=
  alignedSectionCoherence (Descent.baseChangeComparison (a := a) (A := A) f)
    (CocycleDatum.fiberFamily (a := a) (A := A)) (family a Y)
    (leftFiberMap a A f) (rightFiberMap a A f) (primitive_square a A f) hΓ hB hx

/-- The same source derivation, including its endpoint application and raw-type
wrapper, participates in the actual smooth descent/restriction square. -/
theorem universalTransfer_square :
    SectionCoherence a A f Typed.Authoring.UniversalTransfer.context
      Typed.Authoring.UniversalTransfer.type Typed.Authoring.UniversalTransfer.proof :=
  sectionCoherence a A f Typed.Authoring.UniversalTransfer.context
    Typed.Authoring.UniversalTransfer.type Typed.Authoring.UniversalTransfer.proof

end SquareKit.SmoothQuotientGeneratedBaseChange
