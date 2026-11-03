import SquareKit.Internal.ArrowGeometry
import Mathlib.CategoryTheory.Monoidal.Closed.Cartesian

/-! The pushout interpretation of an arrow relative to an object, and its
exponential right adjoint. Subterminality is not needed for this adjunction. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SquareKit.Internal.ArrowPushout
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory CategoryTheory.MonoidalClosed
universe v u
variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C] [HasPushouts C]
variable (P : C)

/-- Glue the codomain over `P` onto the domain. -/
def interpretation : Arrow C ⥤ C where
  obj a := pushout (snd P a.left) (P ◁ a.hom)
  map {a b} f := pushout.map _ _ _ _ f.left (P ◁ f.right) (P ◁ f.left)
    (by simp) (by simp only [← whiskerLeft_comp, Arrow.w])
  map_id a := by apply pushout.hom_ext <;> simp
  map_comp f g := by apply pushout.hom_ext <;> simp [Category.assoc, whiskerLeft_comp]

@[reassoc (attr := simp)] theorem inl_map {a b : Arrow C} (f : a ⟶ b) :
    pushout.inl (snd P a.left) (P ◁ a.hom) ≫ (interpretation P).map f =
      f.left ≫ pushout.inl (snd P b.left) (P ◁ b.hom) := by
  simp [interpretation]

@[reassoc (attr := simp)] theorem inr_map {a b : Arrow C} (f : a ⟶ b) :
    pushout.inr (snd P a.left) (P ◁ a.hom) ≫ (interpretation P).map f =
      (P ◁ f.right) ≫ pushout.inr (snd P b.left) (P ◁ b.hom) := by
  simp [interpretation]

/-- Every map of parameter objects induces a transformation of interpretations. -/
def changeParameter {Q : C} (f : P ⟶ Q) : interpretation P ⟶ interpretation Q where
  app a := pushout.map _ _ _ _ (𝟙 _) (f ▷ a.right) (f ▷ a.left)
    (by simp) (by simp [whisker_exchange])
  naturality {a b} g := by
    apply pushout.hom_ext <;>
      simp [interpretation, Category.assoc, whisker_exchange_assoc]

@[simp] theorem changeParameter_id : changeParameter P (𝟙 P) = 𝟙 (interpretation P) := by
  ext a
  apply pushout.hom_ext <;> simp [changeParameter, interpretation]

@[simp] theorem changeParameter_comp {Q R : C} (f : P ⟶ Q) (g : Q ⟶ R) :
    changeParameter P (f ≫ g) = changeParameter P f ≫ changeParameter Q g := by
  ext a
  apply pushout.hom_ext <;> simp [changeParameter, Category.assoc, comp_whiskerRight]

/-- Parameter isomorphisms transport the construction naturally. -/
def changeParameterIso {Q : C} (e : P ≅ Q) : interpretation P ≅ interpretation Q where
  hom := changeParameter P e.hom
  inv := changeParameter Q e.inv
  hom_inv_id := by rw [← changeParameter_comp, e.hom_inv_id, changeParameter_id]
  inv_hom_id := by rw [← changeParameter_comp, e.inv_hom_id, changeParameter_id]

variable [Closed P]

/-- The exponential arrow sends a value to its constant function on `P`. -/
def rightAdjoint : C ⥤ Arrow C where
  obj T := Arrow.mk (curry (snd P T))
  map {T U} f := Arrow.homMk f ((ihom P).map f) (by
    dsimp only [Arrow.mk_hom]
    rw [← curry_natural_left, ← curry_natural_right, whiskerLeft_snd]; rfl)

/-- Maps out of the pushout are exactly squares into the exponential arrow. -/
def homEquiv (a : Arrow C) (T : C) :
    ((interpretation P).obj a ⟶ T) ≃ (a ⟶ (rightAdjoint P).obj T) where
  toFun f := Arrow.homMk (pushout.inl _ _ ≫ f) (curry (pushout.inr _ _ ≫ f)) (by
    change _ ≫ curry (snd P T) = _
    rw [← curry_natural_left, whiskerLeft_snd, ← curry_natural_left]
    congr 1
    simp only [← Category.assoc, pushout.condition])
  invFun f := pushout.desc f.left (uncurry f.right) (by
    have w := congrArg uncurry (Arrow.w f)
    simpa only [rightAdjoint, Arrow.mk_hom, uncurry_natural_left, uncurry_curry,
      whiskerLeft_snd] using w)
  left_inv f := by
    apply pushout.hom_ext <;> simp
  right_inv f := by
    apply Arrow.hom_ext <;> simp

/-- The pushout interpretation has an explicitly constructed right adjoint. -/
def adjunction : interpretation P ⊣ rightAdjoint P :=
  Adjunction.mkOfHomEquiv {
    homEquiv := homEquiv P
    homEquiv_naturality_left_symm := by
      intro a b T f g
      apply pushout.hom_ext <;> simp [homEquiv, uncurry_natural_left]
    homEquiv_naturality_right := by
      intro a T U f g
      apply Arrow.hom_ext <;> simp [homEquiv, rightAdjoint, Category.assoc,
        curry_natural_right] }

end SquareKit.Internal.ArrowPushout
