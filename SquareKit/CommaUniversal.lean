import SquareKit.CommaLawful
import SquareKit.CommaExact
import Mathlib.CategoryTheory.Comma.Arrow
import Mathlib.CategoryTheory.Whiskering

/-! # The universal property of a lawful comma category

Cones from `X` consist of two functors and a possibly noninvertible natural
transformation. Their morphisms are compatible pairs of natural transformations.
Using another Mathlib comma category supplies their category laws. The raw
construction and its weaker source assumptions remain in `Comma`.

This is the strict hom-category universal property described at
<https://ncatlab.org/nlab/show/comma+category>. The cospan is fixed; changes of
cospan remain available through Mathlib's mixed-variance `Comma.map`.
-/

namespace SquareKit.Comma.Universal

open CategoryTheory CategoryTheory.Functor

set_option autoImplicit false

universe u₁ v₁ u₂ v₂ u₃ v₃ u₄ v₄ u₅ v₅ u₆ v₆

variable {A : Type u₁} {B : Type u₂} {T : Type u₃}
  [Category.{v₁} A] [Category.{v₂} B] [Category.{v₃} T]
  (F : A ⥤ T) (G : B ⥤ T)

/-- Cones over `F, G`, including their compatible transformations. -/
abbrev Cone (X : Type u₄) [Category.{v₄} X] :=
  CategoryTheory.Comma ((whiskeringRight X A T).obj F) ((whiskeringRight X B T).obj G)

variable {X : Type u₄} [Category.{v₄} X]

/-- Lift two functors and their comparison to a functor into the comma category. -/
def lift (P : X ⥤ A) (Q : X ⥤ B) (α : P ⋙ F ⟶ Q ⋙ G) :
    X ⥤ CategoryTheory.Comma F G where
  obj x := ⟨P.obj x, Q.obj x, α.app x⟩
  map f := ⟨P.map f, Q.map f, α.naturality f⟩
  map_id x := CategoryTheory.CommaMorphism.ext (P.map_id x) (Q.map_id x)
  map_comp f g := CategoryTheory.CommaMorphism.ext (P.map_comp f g) (Q.map_comp f g)

@[simp] theorem lift_fst (P : X ⥤ A) (Q : X ⥤ B) (α : P ⋙ F ⟶ Q ⋙ G) :
    lift F G P Q α ⋙ CategoryTheory.Comma.fst F G = P := rfl

@[simp] theorem lift_snd (P : X ⥤ A) (Q : X ⥤ B) (α : P ⋙ F ⟶ Q ⋙ G) :
    lift F G P Q α ⋙ CategoryTheory.Comma.snd F G = Q := rfl

/-- The comparison of an arbitrary functor into the comma category. -/
def comparison (H : X ⥤ CategoryTheory.Comma F G) :
    (H ⋙ CategoryTheory.Comma.fst F G) ⋙ F ⟶
      (H ⋙ CategoryTheory.Comma.snd F G) ⋙ G where
  app x := (H.obj x).hom
  naturality _ _ f := (H.map f).w

@[simp] theorem comparison_lift (P : X ⥤ A) (Q : X ⥤ B) (α : P ⋙ F ⟶ Q ⋙ G) :
    comparison F G (lift F G P Q α) = α := rfl

@[simp] theorem lift_comparison (H : X ⥤ CategoryTheory.Comma F G) :
    lift F G (H ⋙ CategoryTheory.Comma.fst F G)
      (H ⋙ CategoryTheory.Comma.snd F G) (comparison F G H) = H := rfl

/-- A transformation is determined by its two projections. -/
@[ext] theorem natTrans_ext {H K : X ⥤ CategoryTheory.Comma F G} {α β : H ⟶ K}
    (hl : whiskerRight α (CategoryTheory.Comma.fst F G) =
      whiskerRight β (CategoryTheory.Comma.fst F G))
    (hr : whiskerRight α (CategoryTheory.Comma.snd F G) =
      whiskerRight β (CategoryTheory.Comma.snd F G)) : α = β := by
  ext x
  · exact congrArg (fun η => η.app x) hl
  · exact congrArg (fun η => η.app x) hr

/-- The projection part of the universal property, on functors and transformations. -/
def toCones : (X ⥤ CategoryTheory.Comma F G) ⥤ Cone F G X where
  obj H := ⟨H ⋙ CategoryTheory.Comma.fst F G,
    H ⋙ CategoryTheory.Comma.snd F G, comparison F G H⟩
  map η := ⟨whiskerRight η (CategoryTheory.Comma.fst F G),
    whiskerRight η (CategoryTheory.Comma.snd F G), by
      ext x
      exact (η.app x).w⟩

/-- The lifting part of the universal property, including all transformations. -/
def fromCones : Cone F G X ⥤ (X ⥤ CategoryTheory.Comma F G) where
  obj S := lift F G S.left S.right S.hom
  map η := {
    app := fun x => ⟨η.left.app x, η.right.app x, congrArg (fun α => α.app x) η.w⟩
    naturality := fun _ _ f => CategoryTheory.CommaMorphism.ext
      (η.left.naturality f) (η.right.naturality f) }

/-- Strict recovery is stronger than merely recovering up to natural isomorphism. -/
theorem toCones_fromCones : toCones F G (X := X) ⋙ fromCones F G = 𝟭 _ := rfl

theorem fromCones_toCones : fromCones F G (X := X) ⋙ toCones F G = 𝟭 _ := rfl

/-- The hom-category universal property, retaining noninvertible comparisons and maps. -/
def equivalence : (X ⥤ CategoryTheory.Comma F G) ≌ Cone F G X where
  functor := toCones F G
  inverse := fromCones F G
  unitIso := Iso.refl _
  counitIso := Iso.refl _
  functor_unitIso_comp _ := by
    change (toCones F G).map (𝟙 _) ≫ 𝟙 _ = _
    simp

/-- Reindex a cone using an ordinary functor. Its morphisms reindex as well. -/
def precompose {Y : Type u₅} [Category.{v₅} Y] (J : Y ⥤ X) :
    Cone F G X ⥤ Cone F G Y where
  obj S := ⟨J ⋙ S.left, J ⋙ S.right, {
    app := fun y => S.hom.app (J.obj y)
    naturality := fun _ _ f => S.hom.naturality (J.map f) }⟩
  map η := ⟨whiskerLeft J η.left, whiskerLeft J η.right, by
    ext y
    exact congrArg (fun α => α.app (J.obj y)) η.w⟩

@[simp] theorem precompose_id : precompose F G (𝟭 X) = 𝟭 _ := rfl

@[simp] theorem precompose_comp {Y : Type u₅} {Z : Type u₆}
    [Category.{v₅} Y] [Category.{v₆} Z] (J : Y ⥤ X) (K : Z ⥤ Y) :
    precompose F G (K ⋙ J) = precompose F G J ⋙ precompose F G K := rfl

/-- The universal property is natural in the test category, on objects and arrows. -/
theorem toCones_precompose {Y : Type u₅} [Category.{v₅} Y] (J : Y ⥤ X) :
    (whiskeringLeft Y X (CategoryTheory.Comma F G)).obj J ⋙ toCones F G =
      toCones F G ⋙ precompose F G J := rfl

theorem fromCones_precompose {Y : Type u₅} [Category.{v₅} Y] (J : Y ⥤ X) :
    precompose F G J ⋙ fromCones F G =
      fromCones F G ⋙ (whiskeringLeft Y X (CategoryTheory.Comma F G)).obj J := rfl

/-- Reindexing also acts on transformations of the test functor. -/
def precomposeNat {Y : Type u₅} [Category.{v₅} Y] {J K : Y ⥤ X} (η : J ⟶ K) :
    precompose F G J ⟶ precompose F G K where
  app S := ⟨whiskerRight η S.left, whiskerRight η S.right, by
    ext y
    exact S.hom.naturality (η.app y)⟩
  naturality S S' f := by
    apply CategoryTheory.CommaMorphism.ext <;> ext y
    · exact (f.left.naturality (η.app y)).symm
    · exact (f.right.naturality (η.app y)).symm

@[simp] theorem precomposeNat_id {Y : Type u₅} [Category.{v₅} Y] (J : Y ⥤ X) :
    precomposeNat F G (𝟙 J) = 𝟙 (precompose F G J) := by
  ext S y <;> simp [precomposeNat, precompose]

@[simp] theorem precomposeNat_comp {Y : Type u₅} [Category.{v₅} Y]
    {J K L : Y ⥤ X} (η : J ⟶ K) (θ : K ⟶ L) :
    precomposeNat F G (η ≫ θ) = precomposeNat F G η ≫ precomposeNat F G θ := by
  ext S y <;> simp [precomposeNat, precompose]

/-- Naturality of the universal property at the transformation level. -/
theorem toCones_precomposeNat {Y : Type u₅} [Category.{v₅} Y]
    {J K : Y ⥤ X} (η : J ⟶ K) :
    whiskerRight ((whiskeringLeft Y X (CategoryTheory.Comma F G)).map η) (toCones F G) =
      whiskerLeft (toCones F G) (precomposeNat F G η) := rfl

theorem fromCones_precomposeNat {Y : Type u₅} [Category.{v₅} Y]
    {J K : Y ⥤ X} (η : J ⟶ K) :
    whiskerRight (precomposeNat F G η) (fromCones F G) =
      whiskerLeft (fromCones F G)
        ((whiskeringLeft Y X (CategoryTheory.Comma F G)).map η) := rfl

theorem precomposeNat_whiskerLeft {Y : Type u₅} {Z : Type u₆}
    [Category.{v₅} Y] [Category.{v₆} Z] {J K : Y ⥤ X} (η : J ⟶ K) (L : Z ⥤ Y) :
    precomposeNat F G (whiskerLeft L η) =
      whiskerRight (precomposeNat F G η) (precompose F G L) := rfl

theorem precomposeNat_whiskerRight {Y : Type u₅} {Z : Type u₆}
    [Category.{v₅} Y] [Category.{v₆} Z] {J K : Z ⥤ Y} (η : J ⟶ K) (L : Y ⥤ X) :
    precomposeNat F G (whiskerRight η L) =
      whiskerLeft (precompose F G L) (precomposeNat F G η) := rfl

end SquareKit.Comma.Universal
