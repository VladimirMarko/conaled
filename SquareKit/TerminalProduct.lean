import SquareKit.Family
import Mathlib.CategoryTheory.LocallyCartesianClosed.Sections
import Mathlib.CategoryTheory.LocallyCartesianClosed.ExponentiableMorphism

/-! Experimental dependent products along terminal maps. The adjunction uses
Mathlib's ordinary `Over.pullback`, hence the same pullbacks as `Family.reindex`.
A local product choice mediates the comparison; it does not replace global
chosen limits. -/
noncomputable section
namespace SquareKit.TerminalProduct
open CategoryTheory MonoidalCategory CartesianMonoidalCategory
universe u v
variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
variable (Γ : C) [Limits.HasPullbacks C]

-- Capture the existing limit choice before introducing the product adapter.
local instance : Limits.HasPullbacksAlong (toUnit Γ) := inferInstance

local instance : ChosenPullbacksAlong (toUnit Γ) :=
  ChosenPullbacksAlong.cartesianMonoidalCategoryToUnit _

/-- Product choice of the terminal-map pullback, in Mathlib's chosen interface. -/
abbrev productPullback : Over (𝟙_ C) ⥤ Over Γ := ChosenPullbacksAlong.pullback (toUnit Γ)

/-- The terminal slice's forgetful equivalence turns this choice into toOver. -/
def productComparison : productPullback Γ ≅ (equivToOverUnit C).functor ⋙ toOver Γ :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro X Y f
    apply Over.OverMorphism.ext
    change (f.left ▷ Γ) ≫ 𝟙 _ = 𝟙 _ ≫ (f.left ▷ Γ)
    simp)

/-- Compare the actual limit pullbacks with the product choice, naturally. -/
def pullbackComparison : Over.pullback (toUnit Γ) ≅ productPullback Γ :=
  (Over.mapPullbackAdj (toUnit Γ)).rightAdjointUniq
    (ChosenPullbacksAlong.mapPullbackAdj (toUnit Γ))

@[reassoc (attr := simp)] theorem comparison_fst (X : Over (𝟙_ C)) :
    ((pullbackComparison Γ).hom.app X).left ≫ fst X.left Γ =
      Limits.pullback.fst X.hom (toUnit Γ) := by
  have h := Adjunction.rightAdjointUniq_hom_counit
    (Over.mapPullbackAdj (toUnit Γ)) (ChosenPullbacksAlong.mapPullbackAdj (toUnit Γ))
  have hh := congrArg (fun k => (k.app X).left) h
  change ((pullbackComparison Γ).hom.app X).left ≫ fst X.left Γ =
    (𝟙 _) ≫ Limits.pullback.fst X.hom (toUnit Γ) at hh
  simpa only [Category.id_comp] using hh

@[reassoc (attr := simp)] theorem comparison_snd (X : Over (𝟙_ C)) :
    ((pullbackComparison Γ).hom.app X).left ≫ snd X.left Γ =
      Family.reindex X.hom (toUnit Γ) := Over.w _

variable [Closed Γ] [BraidedCategory C]
local instance : ChosenPullbacksAlong (curryRightUnitorHom Γ) :=
  ChosenPullbacksAlong.ofHasPullbacksAlong _

/-- The dependent product is the internal section object, placed over the unit. -/
def pi : Over Γ ⥤ Over (𝟙_ C) := Over.sections Γ ⋙ (equivToOverUnit C).inverse

/-- Right adjoint to actual pullback along Γ → 1, not merely to toOver. -/
def adjunction : Over.pullback (toUnit Γ) ⊣ pi Γ :=
  (((equivToOverUnit C).toAdjunction.comp (Over.toOverSectionsAdj Γ)).ofNatIsoLeft
    (productComparison Γ).symm).ofNatIsoLeft (pullbackComparison Γ).symm

/-- Explicit exponentiability for the ordinary limit-based pullback choice. -/
@[instance_reducible] def exponentiable :
    letI := ChosenPullbacksAlong.ofHasPullbacksAlong (toUnit Γ)
    ExponentiableMorphism (toUnit Γ) := by
  letI := ChosenPullbacksAlong.ofHasPullbacksAlong (toUnit Γ)
  exact ⟨pi Γ, adjunction Γ⟩

abbrev homEquiv (X : Over (𝟙_ C)) (A : Over Γ) := (adjunction Γ).homEquiv X A

@[simp] theorem beta (X : Over (𝟙_ C)) (A : Over Γ)
    (f : (Over.pullback (toUnit Γ)).obj X ⟶ A) :
    (homEquiv Γ X A).symm (homEquiv Γ X A f) = f := (homEquiv Γ X A).left_inv f

@[simp] theorem eta (X : Over (𝟙_ C)) (A : Over Γ) (f : X ⟶ (pi Γ).obj A) :
    homEquiv Γ X A ((homEquiv Γ X A).symm f) = f := (homEquiv Γ X A).right_inv f

theorem parameter_natural {X Y : Over (𝟙_ C)} (g : Y ⟶ X) (A : Over Γ)
    (f : (Over.pullback (toUnit Γ)).obj X ⟶ A) :
    homEquiv Γ Y A ((Over.pullback (toUnit Γ)).map g ≫ f) = g ≫ homEquiv Γ X A f :=
  (adjunction Γ).homEquiv_naturality_left g f

theorem family_natural (X : Over (𝟙_ C)) {A B : Over Γ} (g : A ⟶ B)
    (f : (Over.pullback (toUnit Γ)).obj X ⟶ A) :
    homEquiv Γ X B (f ≫ g) = homEquiv Γ X A f ≫ (pi Γ).map g :=
  (adjunction Γ).homEquiv_naturality_right f g

/-- The new transpose agrees with section currying after the pullback comparison. -/
theorem curry_left (X : Over (𝟙_ C)) (A : Over Γ)
    (f : (Over.pullback (toUnit Γ)).obj X ⟶ A) :
    (homEquiv Γ X A f).left =
      (Over.toOverSectionsAdj Γ).homEquiv X.left A
        ((pullbackComparison Γ).inv.app X ≫ f) := by
  unfold homEquiv adjunction
  erw [Adjunction.homEquiv_ofNatIsoLeft_apply,
    Adjunction.homEquiv_ofNatIsoLeft_apply, Adjunction.comp_homEquiv]
  change (𝟙 X.left) ≫ (Over.toOverSectionsAdj Γ).homEquiv X.left A
    (𝟙 _ ≫ ((pullbackComparison Γ).inv.app X ≫ f)) = _
  simp

/-- Evaluation agrees with the section adjunction after the inverse comparison. -/
theorem uncurry_compare (X : Over (𝟙_ C)) (A : Over Γ) (f : X ⟶ (pi Γ).obj A) :
    (pullbackComparison Γ).inv.app X ≫ (homEquiv Γ X A).symm f =
      ((Over.toOverSectionsAdj Γ).homEquiv X.left A).symm f.left := by
  apply ((Over.toOverSectionsAdj Γ).homEquiv X.left A).injective
  erw [Equiv.apply_symm_apply, ← curry_left, eta]

/-- Both triangle laws for the actual pullback/product adjunction. -/
theorem triangle_left (X : Over (𝟙_ C)) :
    (Over.pullback (toUnit Γ)).map ((adjunction Γ).unit.app X) ≫
      (adjunction Γ).counit.app ((Over.pullback (toUnit Γ)).obj X) = 𝟙 _ :=
  (adjunction Γ).left_triangle_components X

theorem triangle_right (A : Over Γ) :
    (adjunction Γ).unit.app ((pi Γ).obj A) ≫
      (pi Γ).map ((adjunction Γ).counit.app A) = 𝟙 _ :=
  (adjunction Γ).right_triangle_components A

end SquareKit.TerminalProduct
