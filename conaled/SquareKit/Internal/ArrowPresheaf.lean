import SquareKit.Internal.ArrowGeometry
import Mathlib.CategoryTheory.Limits.Types.Limits
import Mathlib.CategoryTheory.Limits.Types.Colimits
import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic

/-! A pointwise construction for arrow diagrams of sets. A monotone predicate
selects the codomain where true and the domain where false. Restriction maps
across false to true use the arrow itself. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SquareKit.Internal.ArrowPresheaf
open CategoryTheory CategoryTheory.Limits
universe v u w
variable {D : Type u} [Category.{v} D]
variable (p : D → Prop) (hp : ∀ {X Y : D}, (X ⟶ Y) → p X → p Y)

/-- Selected elements carry the branch witness, which is proposition-valued. -/
def selected (a : Arrow (D ⥤ Type w)) (X : D) : Type w :=
  {_x : a.right.obj X // p X} ⊕ {_x : a.left.obj X // ¬ p X}

/-- Restriction across the boundary uses the original arrow. -/
def restrict (a : Arrow (D ⥤ Type w)) {X Y : D} (f : X ⟶ Y) :
    selected p a X ⟶ selected p a Y := by
  classical
  exact TypeCat.ofHom fun x => match x with
    | .inl x => .inl ⟨a.right.map f x.val, hp f x.property⟩
    | .inr x => if hy : p Y then .inl ⟨a.hom.app Y (a.left.map f x.val), hy⟩
      else .inr ⟨a.left.map f x.val, hy⟩

/-- The selected sets form a diagram, including boundary-crossing maps. -/
def object (a : Arrow (D ⥤ Type w)) : D ⥤ Type w where
  obj := selected p a
  map := restrict p hp a
  map_id X := by
    classical
    ext x
    cases x with
    | inl x => simp [restrict]
    | inr x => simp [restrict, x.property]
  map_comp {X Y Z} f g := by
    classical
    ext x
    cases x with
    | inl x => simp [restrict]
    | inr x =>
      by_cases hy : p Y
      · have hz := hp g hy
        simp only [restrict, types_comp_apply, TypeCat.hom_ofHom, dite_eq_left hy,
          dite_eq_left hz, Functor.map_comp]
        congr 2
        exact types_congr_hom (a.hom.naturality g) (a.left.map f x.val)
      · by_cases hz : p Z <;> simp [restrict, hy, hz]

/-- A square induces a map between the selected diagrams. -/
def map {a b : Arrow (D ⥤ Type w)} (f : a ⟶ b) : object p hp a ⟶ object p hp b where
  app X := TypeCat.ofHom fun x => match x with
    | .inl x => .inl ⟨f.right.app X x.val, x.property⟩
    | .inr x => .inr ⟨f.left.app X x.val, x.property⟩
  naturality {X Y} g := by
    classical
    ext x
    cases x with
    | inl x =>
      change Sum.inl _ = Sum.inl _
      congr 2
      exact types_congr_hom (f.right.naturality g) x.val
    | inr x =>
      by_cases hy : p Y
      · have w := congrArg (fun α => α.app Y) (Arrow.w f)
        dsimp at w
        have n := f.left.naturality g
        have eq : (a.left.map g ≫ a.hom.app Y) ≫ f.right.app Y =
            f.left.app X ≫ b.left.map g ≫ b.hom.app Y := by
          rw [Category.assoc, ← w, ← Category.assoc, n, Category.assoc]
        dsimp [object, restrict]
        simp only [dite_eq_left hy]
        congr 2
        exact types_congr_hom eq x.val
      · dsimp [object, restrict]
        simp only [dite_eq_right hy]
        congr 2
        exact types_congr_hom (f.left.naturality g) x.val

/-- The pointwise switch functor. -/
def interpretation : Arrow (D ⥤ Type w) ⥤ (D ⥤ Type w) where
  obj := object p hp
  map := map p hp
  map_id a := by ext X x; cases x <;> rfl
  map_comp f g := by ext X x; cases x <;> rfl

/-- At a true stage, the construction is naturally codomain evaluation. -/
def trueEvaluation (X : D) (h : p X) :
    interpretation p hp ⋙ (evaluation D (Type w)).obj X ≅
      Arrow.rightFunc ⋙ (evaluation D (Type w)).obj X :=
  NatIso.ofComponents (fun a => {
    hom := TypeCat.ofHom fun x => match x with
      | .inl x => x.val
      | .inr x => False.elim (x.property h)
    inv := TypeCat.ofHom fun x => .inl ⟨x, h⟩
    hom_inv_id := by ext x; cases x with
      | inl x => rfl
      | inr x => exact False.elim (x.property h)
    inv_hom_id := rfl }) (by
      intro a b f
      ext x
      cases x with
      | inl x => rfl
      | inr x => exact False.elim (x.property h))

/-- At a false stage, the construction is naturally domain evaluation. -/
def falseEvaluation (X : D) (h : ¬ p X) :
    interpretation p hp ⋙ (evaluation D (Type w)).obj X ≅
      Arrow.leftFunc ⋙ (evaluation D (Type w)).obj X :=
  NatIso.ofComponents (fun a => {
    hom := TypeCat.ofHom fun x => match x with
      | .inl x => False.elim (h x.property)
      | .inr x => x.val
    inv := TypeCat.ofHom fun x => .inr ⟨x, h⟩
    hom_inv_id := by ext x; cases x with
      | inl x => exact False.elim (h x.property)
      | inr x => rfl
    inv_hom_id := rfl }) (by
      intro a b f
      ext x
      cases x with
      | inl x => exact False.elim (h x.property)
      | inr x => rfl)

/-- Pointwise selection preserves limits; no complementedness in a sheaf topos is assumed. -/
instance : PreservesLimitsOfSize.{w, w} (interpretation p hp : Arrow (D ⥤ Type w) ⥤ (D ⥤ Type w)) := by
  classical
  apply preservesLimits_of_evaluation
  intro X
  by_cases h : p X
  · exact preservesLimits_of_natIso (trueEvaluation p hp X h).symm
  · exact preservesLimits_of_natIso (falseEvaluation p hp X h).symm

/-- In particular, finite limits are preserved. -/
instance : PreservesFiniteLimits (interpretation p hp : Arrow (D ⥤ Type w) ⥤ (D ⥤ Type w)) :=
  preservesFiniteLimits_of_preservesFiniteLimitsOfSize.{w} _ (fun _ => inferInstance)

end SquareKit.Internal.ArrowPresheaf

