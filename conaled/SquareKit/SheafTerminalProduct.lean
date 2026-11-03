import SquareKit.TerminalProduct
import SquareKit.SheafSectionsConstant

/-! Experimental terminal-map dependent products in the constructed sheaf
category. The only caller inputs are ordinary sheaves and display maps, with
sections in Type(max u v). No arbitrary-base right adjoints are asserted. -/
noncomputable section
namespace SquareKit.SheafTerminalProduct
open CategoryTheory MonoidalCategory SheafRelation
universe u v
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {Γ A X : Sheaf J (Type (max u v))}

local instance (Γ : Sheaf J (Type (max u v))) : @Closed _ _
    (inferInstance : CartesianMonoidalCategory (Sheaf J (Type (max u v)))).toSemiCartesianMonoidalCategory.toMonoidalCategory Γ := by
  exact (inferInstance : Closed Γ)
local instance : MonoidalCategory (Sheaf J (Type (max u v))) :=
  (inferInstance : CartesianMonoidalCategory (Sheaf J (Type (max u v)))).toSemiCartesianMonoidalCategory.toMonoidalCategory
local instance : BraidedCategory (Sheaf J (Type (max u v))) :=
  BraidedCategory.ofCartesianMonoidalCategory

local instance (Γ : Sheaf J (Type (max u v))) : ChosenPullbacksAlong (curryRightUnitorHom Γ) :=
  ChosenPullbacksAlong.ofHasPullbacksAlong _

abbrev terminalMap (Γ : Sheaf J (Type (max u v))) := CartesianMonoidalCategory.toUnit Γ
abbrev pi (Γ : Sheaf J (Type (max u v))) := TerminalProduct.pi Γ
abbrev adjunction (Γ : Sheaf J (Type (max u v))) := TerminalProduct.adjunction Γ
abbrev object (p : A ⟶ Γ) := ((pi Γ).obj (Over.mk p)).left

/-- The product object's underlying sheaf is precisely the constructed sections. -/
def sectionsIso (p : A ⟶ Γ) : object p ≅ SheafSections.sections p := Iso.refl _

/-- Convert an explicit base-first parameterized section to an actual pullback map. -/
def parameterMap (p : A ⟶ Γ) (f : SheafSections.Param p X) :
    (Over.pullback (terminalMap Γ)).obj ((toOverUnit _).obj X) ⟶ Over.mk p :=
  (TerminalProduct.pullbackComparison Γ).hom.app ((toOverUnit _).obj X) ≫ SheafSections.overEquiv p X f

/-- The new pullback adjunction's transpose agrees with the old section curry. -/
theorem curry_comparison (p : A ⟶ Γ) (f : SheafSections.Param p X) :
    ((adjunction Γ).homEquiv ((toOverUnit _).obj X) (Over.mk p) (parameterMap p f)).left =
      SheafSections.curry p f := by
  rw [TerminalProduct.curry_left]
  change (Over.toOverSectionsAdj Γ).homEquiv X (Over.mk p)
    ((TerminalProduct.pullbackComparison Γ).inv.app ((toOverUnit _).obj X) ≫
      ((TerminalProduct.pullbackComparison Γ).hom.app ((toOverUnit _).obj X) ≫ SheafSections.overEquiv p X f)) = _
  erw [Iso.inv_hom_id_app_assoc]
  rfl

/-- Evaluate the genuine pullback counit through the explicit product comparison. -/
theorem counit_comparison (p : A ⟶ Γ) :
    (SheafSections.parameterComparison Γ (object p)).hom ≫
      ((TerminalProduct.pullbackComparison Γ).inv.app ((pi Γ).obj (Over.mk p))).left ≫
      ((adjunction Γ).counit.app (Over.mk p)).left = SheafSections.evaluation p := by
  have h := TerminalProduct.uncurry_compare Γ ((pi Γ).obj (Over.mk p)) (Over.mk p) (𝟙 _)
  erw [Adjunction.homEquiv_symm_id] at h
  have hl := congrArg (fun k => k.left) h
  change _ = SheafSections.evaluation p
  exact congrArg (fun k => (SheafSections.parameterComparison Γ (object p)).hom ≫ k) hl

/-- Exponentiability uses Mathlib's actual ordinary-limit pullback choice. -/
abbrev exponentiable (Γ : Sheaf J (Type (max u v))) := TerminalProduct.exponentiable Γ

end SquareKit.SheafTerminalProduct
