import SquareKit.Internal.GeometricMorphism

/-! The cone category retains both geometric legs, their invertible comparison,
and pairs of transformations satisfying the comparison square. -/
noncomputable section
set_option autoImplicit false
namespace SquareKit.Internal.GeometricMorphism
open CategoryTheory CategoryTheory.Functor
universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄
variable {G : Type u₁} {F : Type u₂} {B : Type u₃} {C : Type u₄}
variable [Category.{v₁} G] [Category.{v₂} F] [Category.{v₃} B] [Category.{v₄} C]

/-- An invertibly commuting cone, with a specified functor on the first geometric leg. -/
structure Cone (H : GeometricMorphism G F ⥤ GeometricMorphism G B) (π : GeometricMorphism C B) where
  base : GeometricMorphism G F
  lift : Lift (H.obj base) π

namespace Cone
variable {H : GeometricMorphism G F ⥤ GeometricMorphism G B} {π : GeometricMorphism C B}

/-- Both transformations are retained; neither is assumed invertible. -/
structure Hom (k l : Cone H π) where
  base : k.base ⟶ l.base
  top : k.lift.morphism ⟶ l.lift.morphism
  over : whiskerLeft π.inverseImage top ≫ l.lift.comparison.hom =
    k.lift.comparison.hom ≫ H.map base

@[ext] theorem Hom.ext {k l : Cone H π} {α β : Hom k l}
    (hb : α.base = β.base) (ht : α.top = β.top) : α = β := by
  cases α; cases β; cases hb; cases ht; rfl

instance : Category (Cone H π) where
  Hom := Hom
  id k := ⟨𝟙 _, 𝟙 _, by
    rw [H.map_id]
    change (𝟙 _) ≫ _ = _ ≫ (𝟙 _)
    simp⟩
  comp α β := ⟨α.base ≫ β.base, α.top ≫ β.top, by
    change (whiskerLeft π.inverseImage α.top ≫ whiskerLeft π.inverseImage β.top) ≫ _ = _
    rw [H.map_comp, Category.assoc, β.over,
      ← Category.assoc, α.over, Category.assoc]
    rfl⟩
  id_comp α := Hom.ext (Category.id_comp _) (Category.id_comp _)
  comp_id α := Hom.ext (Category.comp_id _) (Category.comp_id _)
  assoc α β γ := Hom.ext (Category.assoc _ _ _) (Category.assoc _ _ _)

/-- The first projection keeps the actual base transformation. -/
def baseFunctor : Cone H π ⥤ GeometricMorphism G F where
  obj k := k.base
  map α := α.base

/-- The second projection keeps the actual transformation into the classifier. -/
def topFunctor : Cone H π ⥤ GeometricMorphism G C where
  obj k := k.lift.morphism
  map α := α.top
end Cone
end SquareKit.Internal.GeometricMorphism

namespace SquareKit.Internal.GeometricMorphism
open CategoryTheory CategoryTheory.Functor
universe v₁ v₂ v₃ u₁ u₂ u₃
variable {G : Type u₁} {B : Type u₂} {C : Type u₃}
variable [Category.{v₁} G] [Category.{v₂} B] [Category.{v₃} C]
variable (π : GeometricMorphism C B)

/-- A geometric morphism has its canonical cone over its composite with the projection. -/
def canonicalCone : GeometricMorphism G C ⥤ Cone (𝟭 (GeometricMorphism G B)) π where
  obj k := ⟨k.comp π, ⟨k, Iso.refl _⟩⟩
  map α := ⟨whiskerLeft π.inverseImage α, α, by
    change whiskerLeft π.inverseImage α ≫ 𝟙 _ = 𝟙 _ ≫ whiskerLeft π.inverseImage α
    simp⟩
  map_id _ := Cone.Hom.ext rfl rfl
  map_comp _ _ := Cone.Hom.ext rfl rfl

/-- An arbitrary choice of base leg and comparison is categorically equivalent to its top leg. -/
def canonicalConeEquivalence : GeometricMorphism G C ≌ Cone (𝟭 (GeometricMorphism G B)) π where
  functor := canonicalCone π
  inverse := Cone.topFunctor
  unitIso := NatIso.ofComponents (fun _ => Iso.refl _) (by intros; exact (Category.comp_id _).trans (Category.id_comp _).symm)
  counitIso := NatIso.ofComponents (fun k => {
    hom := ⟨k.lift.comparison.hom, 𝟙 _, by
      change 𝟙 _ ≫ k.lift.comparison.hom = 𝟙 _ ≫ k.lift.comparison.hom
      rfl⟩
    inv := ⟨k.lift.comparison.inv, 𝟙 _, by
      change 𝟙 _ ≫ 𝟙 _ = k.lift.comparison.hom ≫ k.lift.comparison.inv
      simp⟩
    hom_inv_id := Cone.Hom.ext (by exact k.lift.comparison.hom_inv_id) (Category.id_comp _)
    inv_hom_id := Cone.Hom.ext (by exact k.lift.comparison.inv_hom_id) (Category.id_comp _) }) (by
      intro k l α
      apply Cone.Hom.ext
      · exact α.over
      · change α.top ≫ 𝟙 _ = 𝟙 _ ≫ α.top
        simp)
  functor_unitIso_comp X := by
    apply Cone.Hom.ext
    · change 𝟙 _ ≫ 𝟙 _ = 𝟙 _
      simp
    · exact Category.id_comp _
end SquareKit.Internal.GeometricMorphism

namespace SquareKit.Internal.GeometricMorphism.Cone
open CategoryTheory CategoryTheory.Functor
universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄
variable {G : Type u₁} {F : Type u₂} {B : Type u₃} {C : Type u₄}
variable [Category.{v₁} G] [Category.{v₂} F] [Category.{v₃} B] [Category.{v₄} C]
variable {H : GeometricMorphism G F ⥤ GeometricMorphism G B} {π : GeometricMorphism C B}
variable {h : GeometricMorphism G F} {k l : Lift (H.obj h) π}

/-- An isomorphism in a fixed fiber retains both legs as a cone isomorphism. -/
def isoOfLift (e : k ≅ l) : (⟨h, k⟩ : Cone H π) ≅ ⟨h, l⟩ where
  hom := ⟨𝟙 _, e.hom.transformation, by
    rw [H.map_id]
    change _ = k.comparison.hom ≫ 𝟙 (H.obj h).inverseImage
    rw [Category.comp_id]
    exact e.hom.over⟩
  inv := ⟨𝟙 _, e.inv.transformation, by
    rw [H.map_id]
    change _ = l.comparison.hom ≫ 𝟙 (H.obj h).inverseImage
    rw [Category.comp_id]
    exact e.inv.over⟩
  hom_inv_id := Hom.ext (Category.id_comp _) (congrArg Lift.Hom.transformation e.hom_inv_id)
  inv_hom_id := Hom.ext (Category.id_comp _) (congrArg Lift.Hom.transformation e.inv_hom_id)
end SquareKit.Internal.GeometricMorphism.Cone
