import SquareKit.SmoothQuotientCechLocalSignature
import SquareKit.SmoothQuotientGeneratedMatching
import SquareKit.Internal.PathTransport.AlignedSignatureComparison

/-! Generated local evaluation and the actual generated overlap comparison.
The source consists of interpretations over independent primitive matching. -/
noncomputable section
namespace SquareKit.SmoothQuotientCechLocal
open CategoryTheory CategoryTheory.Functor SheafActionQuotient SmoothOpenSite
open SmoothQuotientDeformations Internal.PathTransport GroupoidModel Comparison
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {H : Type} [Group H] {M X Y : Sheaf topology Type}
variable (a : Action (locallyConstantGroup H) M) (A : SplitSheaf.Ty X)

/-- Evaluate generated syntax at the supplied local quotient and deformation. -/
def localMap (hΓ : Typed.CtxDeriv.{2} Γ γ) :
    (show Grpd.{1,1} from γ (model a A)) ⥤
      SmoothQuotientGeneratedMatching.context a hΓ (SplitSheaf.Ext A) :=
  generatedContextMap (signature a A) hΓ

def parameterFiber (f : Y ⟶ SplitSheaf.Ext A) :
    SmoothQuotientDeformations.Cech.family (a := a) (A := A) ⟶
      (SheafActionQuotient.Cech.localFunctor ⋙ restriction f) ⋙ family a Y :=
  localFiber a A ≫ whiskerLeft SheafActionQuotient.Cech.localFunctor (restrictionFamily f)

def parameterSignature (f : Y ⟶ SplitSheaf.Ext A) :=
  alignedUniverseSignature (SheafActionQuotient.Cech.localFunctor ⋙ restriction f)
    (SmoothQuotientDeformations.Cech.family (a := a) (A := A))
    (family a Y) (parameterFiber a A f)

/-- Restriction after local evaluation is the generated composite signature. -/
theorem localMap_restriction (hΓ : Typed.CtxDeriv.{2} Γ γ) (f : Y ⟶ SplitSheaf.Ext A) :
    localMap a A hΓ ⋙ SmoothQuotientGeneratedMatching.restriction a hΓ f =
      generatedContextMap (parameterSignature a A f) hΓ :=
  Context.relabel_composition
    (GeneratedComposition.generatedCtx (signature a A)
      (SmoothQuotientComparison.signature (a := a) f) rfl HEq.rfl hΓ)
    _ _ _ _ _ _

/-- Actual generated overlap arrows, obtained from the primitive overlap and
its deformation equation rather than equality of local representatives. -/
def generatedOverlap (hΓ : Typed.CtxDeriv.{2} Γ γ) :
    localMap a A hΓ ⋙ SmoothQuotientGeneratedMatching.restriction a hΓ (SplitSheaf.Cech.first A) ≅
      localMap a A hΓ ⋙ SmoothQuotientGeneratedMatching.restriction a hΓ (SplitSheaf.Cech.second A) :=
  eqToIso (localMap_restriction a A hΓ (SplitSheaf.Cech.first A)) ≪≫
    alignedContextComparison (overlap a A)
      (SmoothQuotientDeformations.Cech.family (a := a) (A := A))
      (family a (SplitSheaf.Cech.double A))
      (firstFiber a A) (secondFiber a A) (overlap_square a A) hΓ ≪≫
    (eqToIso (localMap_restriction a A hΓ (SplitSheaf.Cech.second A))).symm

end SquareKit.SmoothQuotientCechLocal
