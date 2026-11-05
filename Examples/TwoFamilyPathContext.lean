import SquareKit.Internal.PathTransport.TwoFamilyPathContext
import Examples.TwoOpenIdentityHigher

/-! The full path context retains the integer boundary relating path arrows. -/
noncomputable section
namespace Examples.TwoFamilyPathContext
open CategoryTheory Bicategory SquareKit
open SquareKit.Internal.PathTransport
open Examples.TwoOpenIdentityHigher
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

local instance : IsGroupoid B where
  all_isIso f := by
    obtain ⟨g, h, k⟩ := DoubleDelooping.one_inverse (Multiplicative ℤ) f
    exact ⟨⟨g, h, k⟩⟩
local instance : ∀ x, IsGroupoid (integerFamily.obj x) := fun _ => inferInstanceAs (IsGroupoid B)
local instance : ∀ x, IsLocallyGroupoid (integerFamily.obj x) := fun _ =>
  inferInstanceAs (IsLocallyGroupoid B)

def pathPoint : TwoFamily.PathContext integerFamily :=
  TwoFamily.pathObject integerFamily point point point arrow

/-- Integers are genuine arrows in the path context's identity fiber. -/
def pathArrow (k : ℤ) : pathPoint ⟶ pathPoint :=
  ⟨endpointArrow, Discrete.mk (Multiplicative.ofAdd k)⟩

/-- The second endpoint retains the required base boundary a-b. -/
def pathCell (a b : ℤ) : pathArrow a ⟶ pathArrow b :=
  TwoGroupoidHom.cell (E := TwoFamily.evaluation (TwoFamily.openIdHigher integerFamily) pathPoint.fiber)
    (f := (pathArrow a).fiber) (g := (pathArrow b).fiber) (endpointCell 0 (a-b)) (eqToHom (by
    apply Discrete.ext
    dsimp [TwoFamily.evaluation, TwoFamily.openIdHigher, TwoFamily.openIdCat, TwoFamily.openIdPrelax,
      TwoIdentityTransport.locallyDiscreteEmbedding, TwoIdentityTransport.locallyDiscreteTrans,
      StrictTwoTransformation.evaluation]
    change (show arrow ⟶ arrow from Multiplicative.ofAdd a) =
      (TwoFamily.openIdCell integerFamily (endpointCell 0 (a-b))).app arrow ≫
        (show arrow ⟶ arrow from Multiplicative.ofAdd b)
    rw [show (TwoFamily.openIdCell integerFamily (endpointCell 0 (a-b))).app arrow =
      Multiplicative.ofAdd ((a-b)-0) from endpoint_difference 0 (a-b)]
    change Multiplicative.ofAdd a = Multiplicative.ofAdd b * Multiplicative.ofAdd ((a-b)-0)
    simp))

theorem retained_boundary (a b : ℤ) :
    (pathCell a b).base.fiber.2 = Multiplicative.ofAdd (a-b) := rfl

theorem retained_path_arrow (k : ℤ) : (pathArrow k).fiber.as = Multiplicative.ofAdd k := rfl

example : IsGroupoid (TwoFamily.PathContext integerFamily) := inferInstance
example : IsLocallyGroupoid (TwoFamily.PathContext integerFamily) := inferInstance

end Examples.TwoFamilyPathContext
