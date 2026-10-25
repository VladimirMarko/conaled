import SquareKit.Internal.ArrowPresentation
import SquareKit.Internal.ArrowPushoutModels

/-! Reconstruct an arbitrary geometric lift from the image of the generic
proposition using the canonical pushout presentation of every arrow. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SquareKit.Internal.ArrowReconstruction
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
universe vF vB uF uB
variable {F : Type uF} {B : Type uB} [Category.{vF} F] [Category.{vB} B]
variable [CartesianMonoidalCategory F]
variable [HasInitial B] [HasFiniteLimits B] [HasStrictInitialObjects B]
variable {h : GeometricMorphism F B}
variable (k : GeometricMorphism.Lift h (ArrowGeometry.projection B))

/-- Preservation of the product presentation identifies the image boundary. -/
def boundaryProduct (X : B) :
    k.morphism.inverseImage.obj ((ArrowGeometry.initialArrow B).obj X) ≅
      k.morphism.inverseImage.obj (Sierpinski.generic B) ⊗
        k.morphism.inverseImage.obj ((ArrowGeometry.diagonal B).obj X) :=
  (mapIsLimitOfPreservesOfIsLimit k.morphism.inverseImage _ _
    (ArrowPresentation.boundaryIsProduct X)).conePointUniqueUpToIso
      (tensorProductIsBinaryProduct _ _)

@[reassoc (attr := simp)] theorem boundaryProduct_fst (X : B) :
    (boundaryProduct k X).hom ≫ fst _ _ =
      k.morphism.inverseImage.map (ArrowPresentation.toGeneric X) :=
  (mapIsLimitOfPreservesOfIsLimit k.morphism.inverseImage _ _
    (ArrowPresentation.boundaryIsProduct X)).conePointUniqueUpToIso_hom_comp
      (tensorProductIsBinaryProduct _ _) ⟨WalkingPair.left⟩

@[reassoc (attr := simp)] theorem boundaryProduct_snd (X : B) :
    (boundaryProduct k X).hom ≫ snd _ _ =
      k.morphism.inverseImage.map (ArrowPresentation.boundary X) :=
  (mapIsLimitOfPreservesOfIsLimit k.morphism.inverseImage _ _
    (ArrowPresentation.boundaryIsProduct X)).conePointUniqueUpToIso_hom_comp
      (tensorProductIsBinaryProduct _ _) ⟨WalkingPair.right⟩

/-- Use the specified comparison over the base on the constant factor. -/
def boundaryComparison (X : B) :
    k.morphism.inverseImage.obj ((ArrowGeometry.initialArrow B).obj X) ≅
      k.morphism.inverseImage.obj (Sierpinski.generic B) ⊗ h.inverseImage.obj X :=
  boundaryProduct k X ≪≫ tensorIso (Iso.refl _) (k.comparison.app X)

@[reassoc (attr := simp)] theorem boundaryComparison_fst (X : B) :
    (boundaryComparison k X).hom ≫ fst _ _ =
      k.morphism.inverseImage.map (ArrowPresentation.toGeneric X) := by
  simp [boundaryComparison]
  exact boundaryProduct_fst k X

@[reassoc (attr := simp)] theorem boundaryComparison_snd (X : B) :
    (boundaryComparison k X).hom ≫ snd _ _ =
      k.morphism.inverseImage.map (ArrowPresentation.boundary X) ≫ k.comparison.hom.app X := by
  simp [boundaryComparison]
  exact boundaryProduct_snd_assoc k X (k.comparison.hom.app X)

/-- The boundary comparison respects every base arrow. -/
@[reassoc] theorem boundaryComparison_natural {X Y : B} (f : X ⟶ Y) :
    k.morphism.inverseImage.map ((ArrowGeometry.initialArrow B).map f) ≫
      (boundaryComparison k Y).hom =
    (boundaryComparison k X).hom ≫
      (k.morphism.inverseImage.obj (Sierpinski.generic B) ◁ h.inverseImage.map f) := by
  apply CartesianMonoidalCategory.hom_ext
  · simp only [Category.assoc, boundaryComparison_fst, whiskerLeft_fst,
      boundaryComparison_fst, ← k.morphism.inverseImage.map_comp]
    congr 1
    apply Arrow.hom_ext <;> simp [ArrowGeometry.initialArrow, ArrowPresentation.toGeneric]
  · simp only [Category.assoc, boundaryComparison_snd, whiskerLeft_snd,
      boundaryComparison_snd_assoc]
    rw [← k.comparison.hom.naturality]
    dsimp only [Functor.comp_map, ArrowGeometry.projection]
    simp only [← k.morphism.inverseImage.map_comp_assoc]
    congr 1
    apply congrArg k.morphism.inverseImage.map
    apply Arrow.hom_ext <;> simp [ArrowGeometry.initialArrow, ArrowGeometry.diagonal,
      ArrowPresentation.boundary]

variable [HasPushouts F]

omit [CartesianMonoidalCategory F] [HasFiniteLimits B] [HasStrictInitialObjects B] [HasPushouts F] in
/-- The inverse image of the canonical presentation is still a pushout. -/
theorem presentationPushout (a : Arrow B) :
    IsPushout (k.morphism.inverseImage.map (ArrowPresentation.boundary a.left))
      (k.morphism.inverseImage.map ((ArrowGeometry.initialArrow B).map a.hom))
      (k.morphism.inverseImage.map (ArrowPresentation.domain a))
      (k.morphism.inverseImage.map (ArrowPresentation.codomain a)) :=
  (IsPushout.of_isColimit (ArrowPresentation.isColimit a)).map k.morphism.inverseImage

/-- Compare the image presentation span with the classified span. -/
def spanComparison (a : Arrow B) :
    pushout (k.morphism.inverseImage.map (ArrowPresentation.boundary a.left))
      (k.morphism.inverseImage.map ((ArrowGeometry.initialArrow B).map a.hom)) ⟶
    (ArrowPushout.interpretation (k.morphism.inverseImage.obj (Sierpinski.generic B))).obj
      (h.inverseImage.mapArrow.obj a) :=
  pushout.map _ _ _ _ (k.comparison.hom.app a.left)
    (boundaryComparison k a.right).hom (boundaryComparison k a.left).hom
    (boundaryComparison_snd k a.left).symm (boundaryComparison_natural k a.hom)

instance (a : Arrow B) : IsIso (spanComparison k a) := by
  unfold spanComparison
  infer_instance

/-- Reconstruct the image of any arrow from the actual generic carrier. -/
def objectIso (a : Arrow B) : k.morphism.inverseImage.obj a ≅
    (ArrowPushout.interpretation (k.morphism.inverseImage.obj (Sierpinski.generic B))).obj
      (h.inverseImage.mapArrow.obj a) :=
  (presentationPushout k a).isoPushout ≪≫ asIso (spanComparison k a)

@[reassoc (attr := simp)] theorem objectIso_domain (a : Arrow B) :
    k.morphism.inverseImage.map (ArrowPresentation.domain a) ≫ (objectIso k a).hom =
    k.comparison.hom.app a.left ≫ pushout.inl _ _ := by
  simp [objectIso, spanComparison]

@[reassoc (attr := simp)] theorem objectIso_codomain (a : Arrow B) :
    k.morphism.inverseImage.map (ArrowPresentation.codomain a) ≫ (objectIso k a).hom =
    (boundaryComparison k a.right).hom ≫ pushout.inr _ _ := by
  simp [objectIso, spanComparison]

/-- Reconstruction commutes with arbitrary squares, not only isomorphisms. -/
def reconstruction : k.morphism.inverseImage ≅ h.inverseImage.mapArrow ⋙
    ArrowPushout.interpretation (k.morphism.inverseImage.obj (Sierpinski.generic B)) :=
  NatIso.ofComponents (objectIso k) (by
    intro a b f
    apply (presentationPushout k a).hom_ext
    · dsimp only [Functor.comp_map]
      rw [← Category.assoc, ← k.morphism.inverseImage.map_comp,
        ← ArrowPresentation.domain_natural, k.morphism.inverseImage.map_comp,
        Category.assoc, objectIso_domain]
      rw [objectIso_domain_assoc]
      have n := k.comparison.hom.naturality f.left
      dsimp only [Functor.comp_map, ArrowGeometry.projection] at n
      rw [← Category.assoc, n, Category.assoc]
      exact congrArg (k.comparison.hom.app a.left ≫ ·)
        (ArrowPushout.inl_map _ (h.inverseImage.mapArrow.map f)).symm
    · dsimp only [Functor.comp_map]
      rw [← Category.assoc, ← k.morphism.inverseImage.map_comp,
        ← ArrowPresentation.codomain_natural, k.morphism.inverseImage.map_comp,
        Category.assoc, objectIso_codomain]
      rw [objectIso_codomain_assoc, ← Category.assoc, boundaryComparison_natural,
        Category.assoc]
      exact congrArg ((boundaryComparison k a.right).hom ≫ ·)
        (ArrowPushout.inr_map _ (h.inverseImage.mapArrow.map f)).symm)

end SquareKit.Internal.ArrowReconstruction


