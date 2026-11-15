import SquareKit.SmoothQuotientGeneratedRelativeMatching
import SquareKit.Internal.PathTransport.GeneratedSectionLift

/-! A generated term defines an actual map of the three restriction levels. -/
noncomputable section
namespace SquareKit.SmoothQuotientGeneratedMatching
open CategoryTheory SheafActionQuotient SmoothOpenSite Internal.PathTransport
open GroupoidModel Comparison
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
variable {H : Type} [Group H] {M X : Sheaf topology Type}
variable (a : Action (locallyConstantGroup H) M)
variable {Γ γ B b x ξ} (hΓ : Typed.CtxDeriv.{2} Γ γ)
variable (hB : Typed.TyDeriv.{2} Γ γ B b)
variable (hx : Typed.TmDeriv.{2} Γ γ B b x ξ)

def termDiagram (A : SplitSheaf.Ty X) :
    CechMatching.StrictMap (strictDiagram a hΓ A) ((relativeFamilyData a hΓ hB A).total (relativeFamilyCoherence a hΓ hB A)) where
  localMap := (ξ (SmoothQuotientSource.model a (SplitSheaf.Ext A))).down.lift
  doubleMap := (ξ (SmoothQuotientSource.model a (SplitSheaf.Cech.double A))).down.lift
  tripleMap := (ξ (SmoothQuotientSource.model a (SplitSheaf.Cech.triple A))).down.lift
  first := generatedSectionLift_commutes (SmoothQuotientComparison.signature (SplitSheaf.Cech.first A)) hΓ hB hx
  second := generatedSectionLift_commutes (SmoothQuotientComparison.signature (SplitSheaf.Cech.second A)) hΓ hB hx
  diagonal := generatedSectionLift_commutes (SmoothQuotientComparison.signature (SplitSheaf.Cech.diagonal A)) hΓ hB hx
  firstSecond := generatedSectionLift_commutes (SmoothQuotientComparison.signature (SplitSheaf.Cech.firstSecond A)) hΓ hB hx
  firstThird := generatedSectionLift_commutes (SmoothQuotientComparison.signature (SplitSheaf.Cech.firstThird A)) hΓ hB hx
  secondThird := generatedSectionLift_commutes (SmoothQuotientComparison.signature (SplitSheaf.Cech.secondThird A)) hΓ hB hx

theorem termDiagram_projection (A : SplitSheaf.Ty X) :
    (termDiagram a hΓ hB hx A).comp
      ((relativeFamilyData a hΓ hB A).projection (relativeFamilyCoherence a hΓ hB A)) =
        CechMatching.StrictMap.id (strictDiagram a hΓ A) :=
  CechMatching.StrictMap.ext _ _ rfl rfl rfl

theorem termMatching_projection (A : SplitSheaf.Ty X) :
    (termDiagram a hΓ hB hx A).functor ⋙
      ((relativeFamilyData a hΓ hB A).projection (relativeFamilyCoherence a hΓ hB A)).functor =
        𝟭 (Datum a hΓ A) := by
  rw [← CechMatching.StrictMap.functor_comp, termDiagram_projection, CechMatching.StrictMap.functor_id]
  rfl

/-- A generated section descends over every independently supplied matching base. -/
def termFiber (A : SplitSheaf.Ty X) (d : Datum a hΓ A) :
    CechMatching.Comprehension.Fiber (relativeFamilyData a hΓ hB A)
      (relativeFamilyCoherence a hΓ hB A) d :=
  CechMatching.Comprehension.Fiber.ofDatum ((termDiagram a hΓ hB hx A).functor.obj d)
    (Functor.congr_obj (termMatching_projection a hΓ hB hx A) d)

theorem termFiber_local (A : SplitSheaf.Ty X) (d : Datum a hΓ A) :
    (termFiber a hΓ hB hx A d).localFiber =
      (ξ (SmoothQuotientSource.model a (SplitSheaf.Ext A))).down.obj d.localObject :=
  eq_of_heq (CechMatching.Comprehension.Fiber.localFiber_ofDatum _ _)

end SquareKit.SmoothQuotientGeneratedMatching
