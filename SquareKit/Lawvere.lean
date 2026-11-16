import Mathlib.CategoryTheory.Limits.Preserves.Finite
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

/-! Single-sorted Lawvere theories and their functorial semantics. -/
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SquareKit.Lawvere
open CategoryTheory CategoryTheory.Limits
universe u v u' v' w z

/-- A finite-product category generated, up to isomorphism, by one object.
The nullary power is included. Objects need not be a chosen skeleton. -/
structure Theory where
  Obj : Type u
  category : Category.{v} Obj
  products : @HasFiniteProducts Obj category
  generator : Obj
  generated : ∀ X : Obj, ∃ n : Nat, Nonempty (X ≅ ∏ᶜ (fun _ : Fin n => generator))

attribute [instance] Theory.category Theory.products

/-- A theory morphism preserves finite products and the distinguished generator.
The comparison is an isomorphism, allowing nonskeletal presentations. -/
structure Hom (T : Theory.{u,v}) (U : Theory.{u',v'}) where
  toFunctor : T.Obj ⥤ U.Obj
  preserves : PreservesFiniteProducts toFunctor
  generatorIso : toFunctor.obj T.generator ≅ U.generator

attribute [instance] Hom.preserves

namespace Hom

def id (T : Theory) : Hom T T := ⟨𝟭 _, inferInstance, Iso.refl _⟩
def comp {T : Theory} {U : Theory} {V : Theory} (F : Hom T U) (G : Hom U V) : Hom T V :=
  ⟨F.toFunctor ⋙ G.toFunctor, inferInstance,
    G.toFunctor.mapIso F.generatorIso ≪≫ G.generatorIso⟩
@[simp] theorem id_comp {T U : Theory} (F : Hom T U) : comp (id T) F = F := by
  cases F
  unfold comp id
  congr 1
  ext
  simp

@[simp] theorem comp_id {T U : Theory} (F : Hom T U) : comp F (id U) = F := by
  cases F
  unfold comp id
  congr 1
  ext
  simp

theorem comp_assoc {T U V W : Theory} (F : Hom T U) (G : Hom U V) (H : Hom V W) :
    comp (comp F G) H = comp F (comp G H) := by
  cases F; cases G; cases H
  simp only [comp, Functor.mapIso_trans, Iso.trans_assoc]
  rfl
end Hom

instance : Category Theory.{u,v} where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp
  id_comp := Hom.id_comp
  comp_id := Hom.comp_id
  assoc := Hom.comp_assoc

/-- Models are ordinary finite-product-preserving functors. -/
structure Model (T : Theory.{u,v}) (C : Type w) [Category.{z} C] where
  toFunctor : T.Obj ⥤ C
  preserves : PreservesFiniteProducts toFunctor

attribute [instance] Model.preserves

namespace Model
variable {T : Theory.{u,v}} {U : Theory.{u',v'}} {C : Type w} [Category.{z} C]

/-- Homomorphisms of models are natural transformations. -/
instance : Category (Model T C) where
  Hom M N := M.toFunctor ⟶ N.toFunctor
  id M := 𝟙 M.toFunctor
  comp f g := f ≫ g

/-- Restriction of models is contravariant in the theory. -/
def restrict (F : Hom T U) : Model U C ⥤ Model T C where
  obj M := ⟨F.toFunctor ⋙ M.toFunctor, inferInstance⟩
  map η := { app X := η.app (F.toFunctor.obj X)
             naturality _ _ f := η.naturality (F.toFunctor.map f) }

@[simp] theorem restrict_map_app (F : Hom T U) {M N : Model U C}
    (η : M ⟶ N) (X : T.Obj) :
    ((restrict F).map η).app X = η.app (F.toFunctor.obj X) := rfl

/-- Interpretation sends every chosen finite power to a limiting fan. -/
noncomputable def powerIsLimit (M : Model T C) (n : Nat) :
    IsLimit (Fan.mk (M.toFunctor.obj (∏ᶜ (fun _ : Fin n => T.generator)))
      (fun i => M.toFunctor.map (Pi.π (fun _ : Fin n => T.generator) i))) :=
  isLimitOfHasProductOfPreservesLimit M.toFunctor _

@[simp] theorem restrict_id_obj (M : Model T C) :
    ((restrict (Hom.id T)).obj M).toFunctor = M.toFunctor := rfl

@[simp] theorem restrict_comp_obj {V : Theory} (F : Hom T U) (G : Hom U V)
    (M : Model V C) :
    ((restrict (Hom.comp F G)).obj M).toFunctor =
      ((restrict F).obj ((restrict G).obj M)).toFunctor := rfl
end Model
end SquareKit.Lawvere
