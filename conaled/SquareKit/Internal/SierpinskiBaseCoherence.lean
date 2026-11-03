import SquareKit.Internal.SierpinskiBaseChange
import SquareKit.Internal.SierpinskiSourceCoherence

/-! Identity, composite, and mixed base/source comparisons for the actual arrow
base-change construction. Generic-model evaluation respects these comparisons. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SquareKit.Internal.Sierpinski
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
universe vG vH vE vD vB uG uH uE uD uB
variable {G : Type uG} {H : Type uH} {E : Type uE} {D : Type uD} {B : Type uB}
variable [Category.{vG} G] [Category.{vH} H] [Category.{vE} E] [Category.{vD} D] [Category.{vB} B]
variable [HasFiniteLimits G] [HasFiniteLimits H]
variable [HasInitial E] [HasFiniteLimits E] [HasStrictInitialObjects E]
variable [HasInitial D] [HasFiniteLimits D] [HasStrictInitialObjects D]
variable [HasInitial B] [HasFiniteLimits B] [HasStrictInitialObjects B]

/-- Identity base change agrees with the original lift after the base unitor. -/
def postIdentityIso {h : GeometricMorphism G D}
    (k : GeometricMorphism.Lift h (ArrowGeometry.projection D)) :
    (post (GeometricMorphism.identity D) k).rebase
      (h := h.comp (GeometricMorphism.identity D)) (h' := h) (Functor.leftUnitor h.inverseImage) ≅ k :=
  GeometricMorphism.Lift.isoMk (Functor.leftUnitor k.morphism.inverseImage) (by
    apply NatTrans.ext
    funext X
    simp [post, GeometricMorphism.Lift.rebase, GeometricMorphism.identity,
      ArrowTransport.diagonalIso, ArrowTransport.geometric, ArrowGeometry.projection, ArrowGeometry.diagonal]
    have aux (K : Arrow D ⥤ G) (Y : G) (q : K.obj (Arrow.mk (𝟙 X)) ⟶ Y) :
        𝟙 _ ≫ q = 𝟙 _ ≫ K.map (Arrow.isoMk (Iso.refl X) (Iso.refl X) (by simp)).hom ≫ q ≫ 𝟙 _ := by
      have hi : (Arrow.isoMk (Iso.refl X) (Iso.refl X) (by simp)).hom = 𝟙 (Arrow.mk (𝟙 X)) := by
        apply Arrow.hom_ext <;> rfl
      rw [hi, K.map_id]
      simp
    exact aux k.morphism.inverseImage _ (k.comparison.hom.app X))

/-- Composite base changes agree after the base associator. -/
def postCompIso (b : GeometricMorphism D B) (c : GeometricMorphism E D)
    {h : GeometricMorphism G E} (k : GeometricMorphism.Lift h (ArrowGeometry.projection E)) :
    (post b (post c k)).rebase
      (Functor.associator b.inverseImage c.inverseImage h.inverseImage).symm ≅
      post (c.comp b) k :=
  GeometricMorphism.Lift.isoMk
    (Functor.associator b.inverseImage.mapArrow c.inverseImage.mapArrow k.morphism.inverseImage).symm (by
      apply NatTrans.ext
      funext X
      simp [post, GeometricMorphism.Lift.rebase, GeometricMorphism.comp,
        ArrowTransport.diagonalIso, ArrowTransport.geometric, ArrowGeometry.projection, ArrowGeometry.diagonal]
      simp only [← Functor.map_comp_assoc]
      congr 1
      apply congrArg k.morphism.inverseImage.map
      apply Arrow.hom_ext <;> simp)

/-- Source substitution and base change commute through the inverse-image associator. -/
def mixedIso (b : GeometricMorphism D B) (f : GeometricMorphism H G)
    {h : GeometricMorphism G D} (k : GeometricMorphism.Lift h (ArrowGeometry.projection D)) :
    ((post b k).precomp f).rebase
      (Functor.associator b.inverseImage h.inverseImage f.inverseImage) ≅ post b (k.precomp f) :=
  GeometricMorphism.Lift.isoMk
    (Functor.associator b.inverseImage.mapArrow k.morphism.inverseImage f.inverseImage) (by
      apply NatTrans.ext
      funext X
      simp [post, GeometricMorphism.Lift.rebase, GeometricMorphism.Lift.precomp,
        GeometricMorphism.comp, ArrowGeometry.projection]
      change 𝟙 _ ≫ 𝟙 _ ≫ f.inverseImage.map (k.morphism.inverseImage.map ((ArrowTransport.diagonalIso b.inverseImage).hom.app X)) ≫ f.inverseImage.map (k.comparison.hom.app _) =
        f.inverseImage.map (𝟙 _) ≫ f.inverseImage.map (k.morphism.inverseImage.map ((ArrowTransport.diagonalIso b.inverseImage).hom.app X)) ≫ f.inverseImage.map (k.comparison.hom.app _)
      simp)

/-- Generic interpretation respects the identity base comparison. -/
theorem post_identity {h : GeometricMorphism G D}
    (k : GeometricMorphism.Lift h (ArrowGeometry.projection D)) :
    interpretation.map (postIdentityIso k).hom.transformation =
      (postGeneric (GeometricMorphism.identity D) k).hom := Subsingleton.elim _ _

/-- Generic interpretation respects successive base changes and their associator. -/
theorem post_comp (b : GeometricMorphism D B) (c : GeometricMorphism E D)
    {h : GeometricMorphism G E} (k : GeometricMorphism.Lift h (ArrowGeometry.projection E)) :
    interpretation.map (postCompIso b c k).hom.transformation ≫ (postGeneric (c.comp b) k).hom =
      (postGeneric b (post c k)).hom ≫ (postGeneric c k).hom := Subsingleton.elim _ _

/-- The mixed source/base square commutes on actual generic models. -/
theorem mixed (b : GeometricMorphism D B) (f : GeometricMorphism H G)
    {h : GeometricMorphism G D} (k : GeometricMorphism.Lift h (ArrowGeometry.projection D)) :
    interpretation.map (mixedIso b f k).hom.transformation ≫ (postGeneric b (k.precomp f)).hom ≫
      (sourceComparison h f).hom.app k =
    (sourceComparison (h.comp b) f).hom.app (post b k) ≫
      (SubterminalChange.pull f).map (postGeneric b k).hom := Subsingleton.elim _ _

end SquareKit.Internal.Sierpinski
