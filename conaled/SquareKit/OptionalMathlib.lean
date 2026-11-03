import SquareKit.Optional
import Mathlib.CategoryTheory.Monoidal.Closed.Cartesian
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts.ProdComparison

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SquareKit.OptionalMathlib
open CategoryTheory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
universe u v
variable (C : Type u) [Category.{v} C]

noncomputable def coproducts [HasBinaryCoproducts C] : CoproductOps (ofCategory C) where
  sum a b := a ⨿ b
  inl := coprod.inl
  inr := coprod.inr
  copair f g := coprod.desc f g

theorem coproductCongr [HasBinaryCoproducts C] : CoproductCongr (ofCategory C) (equality _) (coproducts C) where
  copair := by intros; subst_vars; rfl

theorem coproductLaws [HasBinaryCoproducts C] : CoproductLaws (ofCategory C) (equality _) (coproducts C) where
  left f g := coprod.inl_desc f g
  right f g := coprod.inr_desc f g
  eta f := by
    change coprod.desc (coprod.inl ≫ f) (coprod.inr ≫ f) = f
    apply coprod.hom_ext <;> simp

variable [CartesianMonoidalCategory C]
/-- Reversed tensor coordinates align the rightmost argument of our curry
with Mathlib's tensor-left adjunction. This is a chosen binary product. -/
def products : ProductOps (ofCategory C) where
  prod a b := b ⊗ a
  fst := snd _ _
  snd := fst _ _
  pair f g := lift g f

theorem productCongr : ProductCongr (equality (ofCategory C)) (products C) where
  pair := by intros; subst_vars; rfl

theorem productLaws : ProductLaws (equality (ofCategory C)) (products C) where
  fst_pair f g := lift_snd g f
  snd_pair f g := lift_fst g f
  pair_eta f := lift_comp_fst_snd f

/-- Any chosen distributivity isomorphism is accepted independently of closure. -/
noncomputable def distribution [HasBinaryCoproducts C]
    [∀ a b c, IsIso (collect (ofCategory C) (products C) (coproducts C)
      (a := a) (b := b) (c := c))] :
    DistributionOps (ofCategory C) (products C) (coproducts C) where
  distribute := inv (collect (ofCategory C) (products C) (coproducts C))

theorem distributionLaws [HasBinaryCoproducts C]
    [∀ a b c, IsIso (collect (ofCategory C) (products C) (coproducts C)
      (a := a) (b := b) (c := c))] :
    DistributionLaws (ofCategory C) (equality _) (products C) (coproducts C) (distribution C) where
  collect_distribute _ _ _ := IsIso.inv_hom_id _
  distribute_collect _ _ _ := IsIso.hom_inv_id _

variable [MonoidalClosed C]
def closed : ClosedOps (ofCategory C) (products C) where
  exp a b := (ihom a).obj b
  evaluation := (ihom.ev _).app _
  curry := CategoryTheory.MonoidalClosed.curry

theorem closedCongr : ClosedCongr (equality (ofCategory C)) (products C) (closed C) where
  curry := by intros; subst_vars; rfl

/-- Uncurrying is exactly Mathlib's adjunction inverse. -/
theorem uncurry_eq {x a b : C} (f : x ⟶ (ihom a).obj b) :
    (closed C).uncurry f = CategoryTheory.MonoidalClosed.uncurry f := by
  change lift (fst a x) (snd a x ≫ f) ≫ (ihom.ev a).app b = _
  rw [CategoryTheory.MonoidalClosed.uncurry_eq]
  congr 1
  apply CartesianMonoidalCategory.hom_ext <;> simp

theorem closedLaws : ClosedLaws (equality (ofCategory C)) (products C) (closed C) where
  beta f := by
    change (closed C).uncurry (CategoryTheory.MonoidalClosed.curry f) = f
    rw [uncurry_eq]; exact CategoryTheory.MonoidalClosed.uncurry_curry f
  eta f := by
    change CategoryTheory.MonoidalClosed.curry ((closed C).uncurry f) = f
    rw [uncurry_eq]; exact CategoryTheory.MonoidalClosed.curry_uncurry f
  natural {x y a b} f g := by
    change CategoryTheory.MonoidalClosed.curry (lift (fst a y) (snd a y ≫ g) ≫ f) = g ≫ CategoryTheory.MonoidalClosed.curry f
    have h : lift (fst a y) (snd a y ≫ g) = a ◁ g := by
      apply CartesianMonoidalCategory.hom_ext <;> simp
    rw [h]; exact CategoryTheory.MonoidalClosed.curry_natural_left g f
end SquareKit.OptionalMathlib
