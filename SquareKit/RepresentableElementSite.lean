import SquareKit.ElementSite
import Mathlib.CategoryTheory.Sites.Over

/-! The ordinary slice and the elements of a representable, with exact cover transport. -/
set_option autoImplicit false
set_option warningAsError true
namespace SquareKit.RepresentableElementSite
open CategoryTheory Opposite
universe u v
variable {B : Type u} [Category.{v} B] (Γ : B)

/-- Elements of the representable presheaf are arrows into the original context. -/
def elementOver : ElementSite.Site (yoneda.obj Γ) ⥤ Over Γ where
  obj X := Over.mk X.unop.val
  map f := Over.homMk f.unop.hom.unop f.unop.map_val
  map_id _ := rfl
  map_comp _ _ := rfl

def overElement : Over Γ ⥤ ElementSite.Site (yoneda.obj Γ) where
  obj X := op ((yoneda.obj Γ).elementsMk (op X.left) X.hom)
  map f := (Functor.Elements.homMk f.left.op (Over.w f)).op
  map_id _ := rfl
  map_comp _ _ := rfl

def elementOverEquivalence : ElementSite.Site (yoneda.obj Γ) ≌ Over Γ :=
  CategoryTheory.Equivalence.mk (elementOver Γ) (overElement Γ)
    (NatIso.ofComponents (fun X => eqToIso (by cases X; rfl)) (by
      intro X Y f
      apply Quiver.Hom.unop_inj
      apply Functor.Elements.hom_ext
      simp [elementOver, overElement]))
    (NatIso.ofComponents (fun X => eqToIso (by cases X; rfl)) (by
      intro X Y f
      apply Over.OverMorphism.ext
      change f.left ≫ eqToHom (by rfl) = eqToHom (by rfl) ≫ f.left
      simp))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem elementOver_pullback {X : ElementSite.Site (yoneda.obj Γ)}
    (S : Sieve ((elementOver Γ).obj X)) :
    ElementSite.down (yoneda.obj Γ) (S.functorPullback (elementOver Γ)) =
      Sieve.overEquiv _ S := by
  ext Y f
  rw [Sieve.overEquiv_iff]
  constructor
  · rintro ⟨y, h, hs⟩
    cases h
    exact hs
  · intro hs
    exact ⟨_, rfl, hs⟩

theorem overElement_pullback {X : Over Γ}
    (S : Sieve ((overElement Γ).obj X)) :
    Sieve.overEquiv _ (S.functorPullback (overElement Γ)) =
      ElementSite.down (yoneda.obj Γ) S := by
  ext Y f
  rw [Sieve.overEquiv_iff]
  constructor
  · intro hs
    exact ⟨_, rfl, hs⟩
  · rintro ⟨y, h, hs⟩
    cases h
    exact hs

variable (J : GrothendieckTopology B)

instance : (elementOver Γ).IsCocontinuous
    (ElementSite.topology (yoneda.obj Γ) J) (J.over Γ) where
  cover_lift hS := by
    rw [ElementSite.covering_iff, elementOver_pullback]
    exact hS

instance : (overElement Γ).IsCocontinuous
    (J.over Γ) (ElementSite.topology (yoneda.obj Γ) J) where
  cover_lift hS := by
    rw [GrothendieckTopology.mem_over_iff, overElement_pullback]
    exact hS

instance : (elementOverEquivalence Γ).inverse.IsDenseSubsite
    (J.over Γ) (ElementSite.topology (yoneda.obj Γ) J) := by
  let : (elementOverEquivalence Γ).functor.IsCocontinuous
      (ElementSite.topology (yoneda.obj Γ) J) (J.over Γ) :=
    inferInstanceAs ((elementOver Γ).IsCocontinuous _ _)
  let : (elementOverEquivalence Γ).inverse.IsCocontinuous
      (J.over Γ) (ElementSite.topology (yoneda.obj Γ) J) :=
    inferInstanceAs ((overElement Γ).IsCocontinuous _ _)
  exact (elementOverEquivalence Γ).isDenseSubsite_inverse_of_isCocontinuous _ _

instance : (overElement Γ).IsDenseSubsite
    (J.over Γ) (ElementSite.topology (yoneda.obj Γ) J) :=
  inferInstanceAs ((elementOverEquivalence Γ).inverse.IsDenseSubsite _ _)

instance : (elementOver Γ).IsEquivalence :=
  (elementOverEquivalence Γ).isEquivalence_functor

instance : (overElement Γ).IsEquivalence :=
  (elementOverEquivalence Γ).isEquivalence_inverse

instance : (elementOver Γ).IsDenseSubsite
    (ElementSite.topology (yoneda.obj Γ) J) (J.over Γ) := by
  let : (elementOverEquivalence Γ).functor.IsCocontinuous
      (ElementSite.topology (yoneda.obj Γ) J) (J.over Γ) :=
    inferInstanceAs ((elementOver Γ).IsCocontinuous _ _)
  let : (elementOverEquivalence Γ).inverse.IsCocontinuous
      (J.over Γ) (ElementSite.topology (yoneda.obj Γ) J) :=
    inferInstanceAs ((overElement Γ).IsCocontinuous _ _)
  exact (elementOverEquivalence Γ).isDenseSubsite_functor_of_isCocontinuous _ _

end SquareKit.RepresentableElementSite
