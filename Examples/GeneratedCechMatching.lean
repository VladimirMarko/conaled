import SquareKit.SmoothQuotientGeneratedMatching
import SquareKit.Internal.PathTransport.CechMatchingConstant
import Mathlib.CategoryTheory.SingleObj
import Mathlib.Algebra.Group.Int.Defs

/-! Checks for independent generated matching data and its actual restriction
functor. Effectivity beyond the identity-display control remains separate. -/
noncomputable section
namespace Examples.GeneratedCechMatching
open CategoryTheory SquareKit.Internal.PathTransport
open SquareKit.SmoothOpenSite SquareKit.SheafActionQuotient
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

abbrev Loops := SingleObj (Multiplicative ℤ)
abbrev loopObject := SingleObj.star (Multiplicative ℤ)
abbrev oneLoop : loopObject ⟶ loopObject := Multiplicative.ofAdd 1

/-- The matching category retains a concrete nonidentity loop. -/
theorem selected_loop_survives :
    (CechMatching.constantFunctor (Grpd.of Loops)).map oneLoop ≠
      (CechMatching.constantFunctor (Grpd.of Loops)).map (𝟙 loopObject) := by
  intro h
  have hh := (CechMatching.constantFunctor (Grpd.of Loops)).map_injective h
  change (1 : ℤ) = 0 at hh
  exact (by decide : (1 : ℤ) ≠ 0) hh

/-- The same loop is rejected as the overlap of the identity display. -/
example : ¬ ∃ d : CechMatching.Datum (CechMatching.constant (Grpd.of Loops)),
    d.localObject = loopObject ∧ HEq d.overlap (asIso oneLoop) :=
  CechMatching.rejects_nonidentity_overlap (Grpd.of Loops) (asIso oneLoop)
    (by change (1 : ℤ) ≠ 0; decide)

variable {H : Type} [Group H] {M X : Sheaf topology Type}
variable (a : Action (locallyConstantGroup H) M)
variable {Γ γ} (hΓ : Typed.CtxDeriv.{2} Γ γ) (A : SquareKit.SplitSheaf.Ty X)
open SquareKit.SmoothQuotientGeneratedMatching

/-- Every generated judgment uses its original local object restriction. -/
example (x : context a hΓ X) :
    ((restrictionFunctor a hΓ A).obj x).localObject =
      (restriction a hΓ (SquareKit.SplitSheaf.p A)).obj x := rfl

/-- The arrow action is the actual generated restriction, without an
assumption that this restriction is faithful. -/
example {x y : context a hΓ X} (f : x ⟶ y) :
    ((restrictionFunctor a hΓ A).map f).localArrow =
      (restriction a hΓ (SquareKit.SplitSheaf.p A)).map f := rfl

/-- The construction accepts any finite dependent tail derivation, including
pullback and path-reindex constructors, with the same semantic code. -/
example {n Δ Ts} (hT : Typed.TelDeriv.{2} Γ γ n Δ Ts) :
    context a (.telescope hΓ hT) X ⥤ Datum a (.telescope hΓ hT) A :=
  restrictionFunctor a (.telescope hΓ hT) A

end Examples.GeneratedCechMatching
