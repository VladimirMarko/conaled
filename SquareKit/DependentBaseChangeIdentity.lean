import SquareKit.DependentBaseChange

/-! Experimental identity specialization of dependent-product base change.
Chosen pullback functors are normalized by their actual canonical isomorphisms. -/
noncomputable section
namespace SquareKit.DependentBaseChange
open CategoryTheory Limits
universe u v
variable {C : Type u} [Category.{v} C] [HasPullbacks C]
variable {A B : C} (f : A ⟶ B)

omit [HasPullbacks C] in
theorem identitySquare : IsPullback f (𝟙 A) (𝟙 B) f := IsPullback.of_id_snd

@[simp] theorem pullbackId_hom_left (X : Over B) :
    ((Over.pullbackId (X := B)).hom.app X).left = pullback.fst X.hom (𝟙 B) := by
  simp [Over.pullbackId, conjugateIsoEquiv, conjugateEquiv, mateEquiv,
    Over.mapPullbackAdj_counit_app, Over.mapId]

@[reassoc (attr := simp)] theorem pullbackId_inv_fst (X : Over B) :
    ((Over.pullbackId (X := B)).inv.app X).left ≫ pullback.fst X.hom (𝟙 B) = 𝟙 X.left := by
  rw [← pullbackId_hom_left]
  exact congrArg (fun k => k.left) ((Over.pullbackId (X := B)).inv_hom_id_app X)

/-- The identity-square pullback comparison normalizes to the identity. -/
theorem identity_pullback (X : Over B) :
    (Over.pullback f).map ((Over.pullbackId (X := B)).inv.app X) ≫
      (pullbackComparison (identitySquare f)).app X ≫
        (Over.pullbackId (X := A)).hom.app ((Over.pullback f).obj X) = 𝟙 _ := by
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · simp [Category.assoc, pullbackId_hom_left, Over.pullback]
  · simp only [Over.comp_left, Over.id_left, Category.assoc, pullbackId_hom_left]
    erw [pullback.condition]
    simp [Over.pullback]

variable {R : Over A ⥤ Over B} (adj : Over.pullback f ⊣ R)

/-- The expected canonical comparison between the old and identity-pulled products. -/
def identityComparison : R ≅ ExponentiablePullback.squareRightAdjoint f (𝟙 B) adj (identitySquare f) :=
  adj.rightAdjointUniq (ExponentiablePullback.squareAdjunction f (𝟙 B) adj (identitySquare f))

/-- Normalize both identity base changes: the mate is the canonical comparison
of the two actual right adjoints, not an unproved definitional identification. -/
theorem identity_mate (Y : Over A) :
    (Over.pullbackId (X := B)).inv.app (R.obj Y) ≫ (mate (identitySquare f) adj).app Y ≫
      (ExponentiablePullback.squareRightAdjoint f (𝟙 B) adj (identitySquare f)).map
        ((Over.pullbackId (X := A)).hom.app Y) = (identityComparison f adj).hom.app Y := by
  let a := ExponentiablePullback.squareAdjunction f (𝟙 B) adj (identitySquare f)
  apply (a.homEquiv (R.obj Y) Y).symm.injective
  rw [Adjunction.homEquiv_counit, Adjunction.homEquiv_counit]
  simp only [Functor.map_comp, Category.assoc]
  rw [a.counit_naturality]
  rw [← Category.assoc, ← Category.assoc]
  have he := evaluation (identitySquare f) adj Y
  change _ = (Over.pullback f).map ((identityComparison f adj).hom.app Y) ≫ a.counit.app Y
  simp only [Category.assoc]
  erw [← Category.assoc _ (a.counit.app _) _, he]
  simp only [Category.assoc]
  erw [(Over.pullbackId (X := A)).hom.naturality (adj.counit.app Y)]
  simp only [Functor.id_map]
  rw [← Category.assoc, ← Category.assoc]
  erw [Category.assoc _ ((pullbackComparison (identitySquare f)).app (R.obj Y)) _, identity_pullback, Category.id_comp]
  exact (Adjunction.rightAdjointUniq_hom_app_counit adj a Y).symm

end SquareKit.DependentBaseChange
