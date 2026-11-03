import SquareKit.Internal.SliceBaseChange
import SquareKit.Internal.GenericModel

/-! Isomorphic slice objects give geometric lifts over the same base, with
an explicit comparison that preserves the generic diagonal. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SquareKit.Internal.GeometricMorphism
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
universe v u
variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C] [HasPullbacks C]
variable {a b : C} (e : a ≅ b) [Closed a] [Closed b]

/-- The slice equivalence commutes with the two inverse images of the base. -/
def starMapIso : Over.star a ⋙ (Over.mapIso e).functor ≅ Over.star b :=
  NatIso.ofComponents (fun X => Over.isoMk (prod.mapIso e (Iso.refl X)) (by simp)) (by
    intro X Y f
    apply Over.OverMorphism.ext
    apply prod.hom_ext <;> simp)

/-- An isomorphism of slice objects gives an actual geometric lift over the base. -/
def sliceIsoLift : Lift (slice b) (slice a) where
  morphism := ofEquivalence (Over.mapIso e)
  comparison := starMapIso e

/-- Its extracted section becomes the new generic diagonal under the object isomorphism. -/
theorem sliceIsoLift_section :
    (sliceIsoLift e).section ≫ (slice b).inverseImage.map e.hom =
      (identityLift (slice b)).section := by
  have ht : (sliceIsoLift e).terminalIso.inv.left ≫ e.hom =
      (identityLift (slice b)).terminalIso.inv.left := by
    have h₁ := (sliceIsoLift e).terminalIso.inv.w
    have h₂ := (identityLift (slice b)).terminalIso.inv.w
    change (sliceIsoLift e).terminalIso.inv.left ≫ (𝟙 a ≫ e.hom) = _ at h₁
    change (identityLift (slice b)).terminalIso.inv.left ≫ 𝟙 b = _ at h₂
    have reduce {T : C} (d : T ⟶ a) (d' : T ⟶ b)
        (hh : d ≫ (𝟙 a ≫ e.hom) = d' ≫ 𝟙 b) : d ≫ e.hom = d' := by
      simpa only [Category.id_comp, Category.comp_id] using hh
    exact reduce _ _ (h₁.trans h₂.symm)
  apply Over.OverMorphism.ext
  have diagonal {T : C} (d : T ⟶ a) (d' : T ⟶ b) (hh : d ≫ e.hom = d') :
      (d ≫ prod.lift (𝟙 a) (𝟙 a) ≫ prod.map e.hom (𝟙 a)) ≫ prod.map (𝟙 b) e.hom =
        d' ≫ prod.lift (𝟙 b) (𝟙 b) ≫ 𝟙 _ := by
    apply prod.hom_ext <;> simpa using hh
  exact diagonal _ _ ht

end SquareKit.Internal.GeometricMorphism
