import SquareKit.Internal.ArrowGeometry

/-! Pointwise adjunction and finite-limit transport to arrow categories. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SquareKit.Internal.ArrowTransport
open CategoryTheory CategoryTheory.Limits
universe v₁ v₂ u₁ u₂
variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
variable {F : C ⥤ D} {G : D ⥤ C}

/-- Apply an adjunction to both endpoints of an arrow. -/
def adjunction (h : F ⊣ G) : F.mapArrow ⊣ G.mapArrow :=
  Adjunction.mkOfUnitCounit {
    unit := (Functor.mapArrowFunctor C C).map h.unit
    counit := (Functor.mapArrowFunctor D D).map h.counit
    left_triangle := by
      ext a
      · simp
      · simp
    right_triangle := by
      ext a
      · simp
      · simp }

/-- Limits of arrow diagrams are transported endpoint by endpoint. -/
instance [HasInitial C] [PreservesFiniteLimits F] : PreservesFiniteLimits F.mapArrow where
  preservesFiniteLimits J := {
    preservesLimit := fun {K} => {
      preserves := fun {c} hc => ⟨by
        apply Comma.fstSndJointlyReflectLimit
        · exact isLimitOfPreserves F (isLimitOfPreserves Arrow.leftFunc hc)
        · exact isLimitOfPreserves F (isLimitOfPreserves Arrow.rightFunc hc)⟩ } }

/-- A geometric morphism acts pointwise on arrow categories. -/
def geometric [HasInitial C] (h : GeometricMorphism D C) :
    GeometricMorphism (Arrow D) (Arrow C) where
  inverseImage := h.inverseImage.mapArrow
  directImage := h.directImage.mapArrow
  adjunction := adjunction h.adjunction
  leftExact := inferInstance

/-- Applying a functor to identity arrows agrees naturally with the diagonal. -/
def diagonalIso (F : C ⥤ D) : ArrowGeometry.diagonal C ⋙ F.mapArrow ≅
    F ⋙ ArrowGeometry.diagonal D :=
  NatIso.ofComponents (fun X => Arrow.isoMk (Iso.refl _) (Iso.refl _)
    (by simp [ArrowGeometry.diagonal])) (by
      intro X Y f
      apply Arrow.hom_ext <;> simp [ArrowGeometry.diagonal])

end SquareKit.Internal.ArrowTransport

