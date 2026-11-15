import SquareKit.Internal.PathTransport.CechMatchingCone
import SquareKit.Internal.PathTransport.CechMatchingConstant
import Mathlib.CategoryTheory.SingleObj
import Mathlib.Algebra.Group.Int.Defs

/-! A coherent cone retains the selected nonidentity local arrow. -/
noncomputable section
namespace Examples.CechMatchingCone
open CategoryTheory SquareKit.Internal.PathTransport
abbrev Loops := SingleObj (Multiplicative ℤ)
abbrev loopObject := SingleObj.star (Multiplicative ℤ)
abbrev oneLoop : loopObject ⟶ loopObject := Multiplicative.ofAdd 1

theorem identityLaws : CechMatching.ConeLaws
    (D := CechMatching.constant (Grpd.of Loops)) (𝟭 Loops) (Iso.refl _) where
  diagonal := by ext x; change (𝟙 x) = (𝟙 x) ≫ (𝟙 x); simp
  cocycle := by ext x; rfl

def identityCone : Loops ⥤ CechMatching.Datum (CechMatching.constant (Grpd.of Loops)) :=
  CechMatching.coneFunctor (𝟭 Loops) (Iso.refl _) identityLaws

example : (identityCone.map
    oneLoop).localArrow = oneLoop := rfl

example : identityCone.map oneLoop ≠
    identityCone.map (𝟙 loopObject) := by
  intro h
  have he := congrArg CechMatching.Datum.Hom.localArrow h
  change (Multiplicative.ofAdd (1 : ℤ)) = Multiplicative.ofAdd 0 at he
  exact Int.one_ne_zero (congrArg Multiplicative.toAdd he)

end Examples.CechMatchingCone
