import SquareKit.DoubleDelooping
import SquareKit.Internal.PathTransport.TwoFamily
import Mathlib.Algebra.Group.Int.Defs

/-! The abelian-group higher family. A base second cell acts as a first
arrow in the locally discrete delooping fiber. -/
namespace SquareKit.Internal.ModalHigher
open CategoryTheory Bicategory
open SquareKit.Internal.PathTransport
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v w
abbrev Base (G : Type u) := DoubleDelooping.Space (Multiplicative G)
abbrev Fiber (G : Type u) := LocallyDiscrete (SingleObj (Multiplicative G))
variable (G : Type u) [AddCommGroup G]
abbrev point : Base G := DoubleDelooping.point _
abbrev fiberPoint : Fiber G := ⟨SingleObj.star _⟩

/-- Commutativity is precisely the naturality obligation for this action. -/
def action (g : G) : StrictTwoTransformation.Trans
    (StrictPseudofunctor.id (Fiber G)) (StrictPseudofunctor.id (Fiber G)) where
  app _ := Discrete.mk (Multiplicative.ofAdd g)
  naturality f := by
    apply Discrete.ext
    change Multiplicative.ofAdd g * (show Multiplicative G from f.as) =
      (show Multiplicative G from f.as) * Multiplicative.ofAdd g
    exact mul_comm _ _
  naturality₂ _ := congrArg Discrete.Hom.mk rfl

/-- The object fibers are constant, but the higher action is not constant. -/
def family : TwoFamily.Family (Base G) := StrictPseudofunctor.mk'' {
  obj := fun _ => ⟨Fiber G⟩
  map := fun _ => StrictPseudofunctor.id _
  map₂ := fun α => action G (Multiplicative.toAdd α)
  map₂_id := fun _ => by apply StrictTwoTransformation.Trans.ext; intro a; rfl
  map₂_comp := fun α β => by apply StrictTwoTransformation.Trans.ext; intro a; rfl
  map_id := fun _ => rfl
  map_comp := fun _ _ => (StrictTwoTransformation.functor_comp_id _).symm
  map₂_whisker_left := fun f _ _ α => by
    apply StrictTwoTransformation.Trans.ext; intro a
    repeat rw [StrictTwoTransformation.Trans.comp_app]
    repeat rw [StrictTwoTransformation.Trans.eqToHom_app]
    change (show a ⟶ a from Discrete.mk α) = 𝟙 a ≫ Discrete.mk α ≫ 𝟙 a
    cases a with
    | mk a =>
      cases a
      apply Discrete.ext
      change (show Multiplicative G from α) =
        ((1 : Multiplicative G) * (show Multiplicative G from α)) * 1
      simp
  map₂_whisker_right := fun α f => by
    apply StrictTwoTransformation.Trans.ext; intro a
    repeat rw [StrictTwoTransformation.Trans.comp_app]
    repeat rw [StrictTwoTransformation.Trans.eqToHom_app]
    change (show a ⟶ a from Discrete.mk α) = 𝟙 a ≫ Discrete.mk α ≫ 𝟙 a
    cases a with
    | mk a =>
      cases a
      apply Discrete.ext
      change (show Multiplicative G from α) =
        ((1 : Multiplicative G) * (show Multiplicative G from α)) * 1
      simp
}

variable {G} {H : Type v} [AddCommGroup H]
/-- A base homomorphism fixes the sole object and arrow and maps second cells. -/
def baseMap (f : G →+ H) : StrictPseudofunctor (Base G) (Base H) :=
  StrictPseudofunctor.mk'' {
    obj := fun _ => point H
    map := fun _ => SingleObj.star _
    map₂ := fun α => Multiplicative.ofAdd (f (Multiplicative.toAdd α))
    map₂_id := fun _ => f.map_zero
    map₂_comp := fun α β => f.map_add _ _
    map_id := fun _ => rfl
    map_comp := fun _ _ => rfl
    map₂_whisker_left := fun _ _ _ α => by
      change _ = (1 : Multiplicative H) * _ * 1
      simp only [one_mul, mul_one]
      rfl
    map₂_whisker_right := fun α _ => by
      change _ = (1 : Multiplicative H) * _ * 1
      simp only [one_mul, mul_one]
      rfl
  }

/-- Multiplication keys are available for every integer in every abelian group. -/
def multiplier (d : ℤ) : G →+ G where
  toFun g := d • g
  map_zero' := zsmul_zero _
  map_add' := fun x y => zsmul_add x y d
abbrev key (d : ℤ) := baseMap (multiplier (G := G) d)

/-- Pullback retains BH, even when G and H differ. -/
abbrev pulled (f : G →+ H) := TwoFamily.reindex (baseMap f) (family H)

theorem pulled_fiber (f : G →+ H) (x : Base G) :
    (pulled f).obj x = (⟨Fiber H⟩ : StrictTwoCategory) := rfl

/-- Observe the actual family transformation component as its arrow label. -/
def observe (f : G →+ H) (g : G) : H :=
  Multiplicative.toAdd (((pulled f).map₂
    (show (𝟙 (point G)) ⟶ 𝟙 (point G) from Multiplicative.ofAdd g)).app
      (fiberPoint H)).as

theorem pulled_action (f : G →+ H) (g : G) :
    Multiplicative.toAdd (((pulled f).map₂
      (show (𝟙 (point G)) ⟶ 𝟙 (point G) from Multiplicative.ofAdd g)).app
        (fiberPoint H)).as = f g := rfl

theorem observe_eq (f : G →+ H) (g : G) : observe f g = f g :=
  pulled_action f g

variable {J : Type w} [AddCommGroup J]
theorem baseMap_comp (f : G →+ H) (j : H →+ J) :
    (baseMap f).comp (baseMap j) = baseMap (j.comp f) :=
  StrictTwoTransformation.functor_ext rfl

theorem baseMap_id : baseMap (AddMonoidHom.id G) = StrictPseudofunctor.id (Base G) := by
  apply StrictTwoTransformation.functor_ext
  rfl

end SquareKit.Internal.ModalHigher
