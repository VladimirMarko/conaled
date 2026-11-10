import SquareKit.SmoothQuotientCechGeneratedFamilyEvaluation
import SquareKit.Internal.PathTransport.CechMatchingComprehensionTransportCoherence

/-! The actual generated family evaluation commutes with every context arrow
through a selected natural isomorphism, coherent under identity and composition. -/
noncomputable section
namespace SquareKit.SmoothQuotientCechLocal
open CategoryTheory SheafActionQuotient SmoothOpenSite Internal.PathTransport
open GroupoidModel SmoothQuotientGeneratedMatching
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
variable {H : Type} [Group H] {M X : Sheaf topology Type}
variable (a : Action (locallyConstantGroup H) M) (A : SplitSheaf.Ty X)
variable {Γ γ B b} (hΓ : Typed.CtxDeriv.{2} Γ γ) (hB : Typed.TyDeriv.{2} Γ γ B b)

def familyEvaluation_transport {c d : (show Grpd.{1,1} from γ (model a A))}
    (f : c ⟶ d) :
    (b (model a A)).map f ⋙ familyEvaluation a A hΓ hB d ≅
      familyEvaluation a A hΓ hB c ⋙
        (relativeMatchingFamily a hΓ hB A).map ((matchingEvaluation a A hΓ).map f) :=
  CechMatching.Comprehension.Evaluation.transportComparison
    (relativeFamilyData a hΓ hB A) (relativeFamilyCoherence a hΓ hB A)
    (b (model a A)) (matchingEvaluation a A hΓ)
    (totalMatchingEvaluation a A hΓ hB) (totalMatchingEvaluation_projection a A hΓ hB) f

theorem familyEvaluation_transport_id (c : (show Grpd.{1,1} from γ (model a A)))
    (x : (b (model a A)).obj c) :
    (familyEvaluation_transport a A hΓ hB (𝟙 c)).inv.app x ≫
      (familyEvaluation a A hΓ hB c).map
        (eqToHom (CechMatching.Comprehension.Evaluation.sourceId (b (model a A)) c x)) =
    eqToHom (by
      change CechMatching.Comprehension.Fiber.transport
        ((matchingEvaluation a A hΓ).map (𝟙 c)) _ = _
      rw [(matchingEvaluation a A hΓ).map_id, CechMatching.Comprehension.Fiber.transport_id]) :=
  CechMatching.Comprehension.Evaluation.transportComparison_id
    (b (model a A)) (relativeFamilyData a hΓ hB A)
    (relativeFamilyCoherence a hΓ hB A) (matchingEvaluation a A hΓ)
    (totalMatchingEvaluation a A hΓ hB) (totalMatchingEvaluation_projection a A hΓ hB) c x

theorem familyEvaluation_transport_comp {c d e : (show Grpd.{1,1} from γ (model a A))}
    (f : c ⟶ d) (g : d ⟶ e) (x : (b (model a A)).obj c) :
    (familyEvaluation_transport a A hΓ hB (f ≫ g)).inv.app x ≫
      (familyEvaluation a A hΓ hB e).map
        (eqToHom (CechMatching.Comprehension.Evaluation.sourceComp (b (model a A)) f g x)) =
    eqToHom (by
      change CechMatching.Comprehension.Fiber.transport
        ((matchingEvaluation a A hΓ).map (f ≫ g)) _ = _
      rw [(matchingEvaluation a A hΓ).map_comp, CechMatching.Comprehension.Fiber.transport_comp]
      rfl) ≫
      ((relativeMatchingFamily a hΓ hB A).map ((matchingEvaluation a A hΓ).map g)).map
        ((familyEvaluation_transport a A hΓ hB f).inv.app x) ≫
      (familyEvaluation_transport a A hΓ hB g).inv.app (((b (model a A)).map f).obj x) :=
  CechMatching.Comprehension.Evaluation.transportComparison_comp
    (b (model a A)) (relativeFamilyData a hΓ hB A)
    (relativeFamilyCoherence a hΓ hB A) (matchingEvaluation a A hΓ)
    (totalMatchingEvaluation a A hΓ hB) (totalMatchingEvaluation_projection a A hΓ hB) f g x

end SquareKit.SmoothQuotientCechLocal
