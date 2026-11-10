import SquareKit.SmoothQuotientCechSectionDescent
import SquareKit.SmoothQuotientCechBaseEffectivity
import SquareKit.SmoothQuotientCechGeneratedEmpty

/-! Closed base-family sections exercise actual descent with both evaluation
requirements discharged by the empty-context and base-family theorems. -/
noncomputable section
namespace Examples.GeneratedBaseSectionDescent
open CategoryTheory SquareKit SquareKit.SmoothQuotientCechLocal
open SquareKit.SheafActionQuotient SquareKit.SmoothOpenSite
open SquareKit.Internal.PathTransport GroupoidModel
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
variable {H : Type} [Group H] {M X : Sheaf topology Type}
variable (a : Action (locallyConstantGroup H) M) (A : SplitSheaf.Ty X)

variable (s t : Section
  (SmoothQuotientGeneratedMatching.relativeMatchingFamily a
    Typed.CtxDeriv.empty (.base Typed.CtxDeriv.empty) A))

def descended : Section (Typed.baseCode Typed.emptyCode (model a A)) :=
  (matchingSectionResult a A Typed.CtxDeriv.empty (.base Typed.CtxDeriv.empty)
    (familyEvaluation_base_isEquivalence a A Typed.CtxDeriv.empty)).reconstruct s

def selectedVerticalTransformations :
    {η : (descended a A s).lift ⟶ (descended a A t).lift //
      ∀ c, (η.app c).base = 𝟙 c} ≃
    {η : s.lift ⟶ t.lift // ∀ c, (η.app c).base = 𝟙 c} :=
  (matchingSectionResult a A Typed.CtxDeriv.empty (.base Typed.CtxDeriv.empty)
    (familyEvaluation_base_isEquivalence a A Typed.CtxDeriv.empty)).verticalEquiv s t

end Examples.GeneratedBaseSectionDescent
