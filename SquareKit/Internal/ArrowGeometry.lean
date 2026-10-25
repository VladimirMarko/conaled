import SquareKit.Internal.GeometricMorphism
import Mathlib.CategoryTheory.Limits.Comma
import Mathlib.CategoryTheory.Adjunction.Limits

/-! The arrow category has a geometric projection and two geometric points.
These constructions use actual adjunctions and retain all transformations. -/
set_option autoImplicit false
namespace SquareKit.Internal.ArrowGeometry
open CategoryTheory CategoryTheory.Limits
universe v u
variable (C : Type u) [Category.{v} C]

/-- The constant arrow, which is the inverse image of the projection. -/
@[simps] def diagonal : C ⥤ Arrow C where
  obj X := Arrow.mk (𝟙 X)
  map f := Arrow.homMk f f

/-- Codomain evaluation is left adjoint to the constant arrow. -/
def codomainAdjunction : (Arrow.rightFunc : Arrow C ⥤ C) ⊣ diagonal C :=
  Adjunction.mkOfHomEquiv {
    homEquiv := fun X Y => {
      toFun := fun f => Arrow.homMk (X.hom ≫ f) f (by simp [diagonal])
      invFun := fun f => f.right
      left_inv := fun _ => rfl
      right_inv := fun f => by
        apply Arrow.hom_ext
        · simpa [diagonal] using (Arrow.w f).symm
        · rfl }
    homEquiv_naturality_left_symm := by intros; rfl
    homEquiv_naturality_right := by
      intros; apply Arrow.hom_ext
      · exact (Category.assoc _ _ _).symm
      · rfl }

/-- The constant arrow is left adjoint to domain evaluation. -/
def diagonalAdjunction : diagonal C ⊣ (Arrow.leftFunc : Arrow C ⥤ C) :=
  Adjunction.mkOfHomEquiv {
    homEquiv := fun X Y => {
      toFun := fun f => f.left
      invFun := fun f => Arrow.homMk f (f ≫ Y.hom) (by simp [diagonal])
      left_inv := fun f => by
        apply Arrow.hom_ext
        · rfl
        · simpa [diagonal] using (Arrow.w f)
      right_inv := fun _ => rfl }
    homEquiv_naturality_left_symm := by
      intros; apply Arrow.hom_ext
      · rfl
      · exact Category.assoc _ _ _
    homEquiv_naturality_right := by intros; rfl }

instance : (diagonal C).IsRightAdjoint := (codomainAdjunction C).isRightAdjoint
instance : (Arrow.leftFunc : Arrow C ⥤ C).IsRightAdjoint :=
  (diagonalAdjunction C).isRightAdjoint

/-- The structural geometric morphism of the arrow category. -/
def projection : GeometricMorphism (Arrow C) C where
  inverseImage := diagonal C
  directImage := Arrow.leftFunc
  adjunction := diagonalAdjunction C
  leftExact := inferInstance

/-- The terminal-arrow right adjoint to domain evaluation. -/
@[simps] noncomputable def terminalArrow [HasTerminal C] : C ⥤ Arrow C where
  obj X := Arrow.mk (terminal.from X)
  map f := Arrow.homMk f (𝟙 _)

noncomputable def domainAdjunction [HasTerminal C] :
    (Arrow.leftFunc : Arrow C ⥤ C) ⊣ terminalArrow C :=
  Adjunction.mkOfHomEquiv {
    homEquiv := fun X Y => {
      toFun := fun f => Arrow.homMk f (terminal.from X.right) (by simp [terminalArrow])
      invFun := fun f => f.left
      left_inv := fun _ => rfl
      right_inv := fun f => by ext; rfl; exact terminal.hom_ext _ _ }
    homEquiv_naturality_left_symm := by intros; rfl
    homEquiv_naturality_right := by intros; ext; rfl; exact terminal.hom_ext _ _ }

/-- The initial-arrow left adjoint to codomain evaluation. -/
@[simps] noncomputable def initialArrow [HasInitial C] : C ⥤ Arrow C where
  obj X := Arrow.mk (initial.to X)
  map f := Arrow.homMk (𝟙 _) f

noncomputable def initialAdjunction [HasInitial C] :
    initialArrow C ⊣ (Arrow.rightFunc : Arrow C ⥤ C) :=
  Adjunction.mkOfHomEquiv {
    homEquiv := fun X Y => {
      toFun := fun f => f.right
      invFun := fun f => Arrow.homMk (initial.to Y.left) f (by simp [initialArrow])
      left_inv := fun f => by ext; exact initial.hom_ext _ _; rfl
      right_inv := fun _ => rfl }
    homEquiv_naturality_left_symm := by intros; ext; exact initial.hom_ext _ _; rfl
    homEquiv_naturality_right := by intros; rfl }

noncomputable instance [HasInitial C] :
    (Arrow.rightFunc : Arrow C ⥤ C).IsRightAdjoint :=
  (initialAdjunction C).isRightAdjoint

/-- Domain evaluation is the false point. -/
noncomputable def falsePoint [HasTerminal C] : GeometricMorphism C (Arrow C) where
  inverseImage := Arrow.leftFunc
  directImage := terminalArrow C
  adjunction := domainAdjunction C
  leftExact := inferInstance

/-- Codomain evaluation is the true point. -/
def truePoint [HasInitial C] : GeometricMorphism C (Arrow C) where
  inverseImage := Arrow.rightFunc
  directImage := diagonal C
  adjunction := codomainAdjunction C
  leftExact := inferInstance

/-- The structure arrow is a geometric transformation from false to true. -/
def falseToTrue [HasInitial C] [HasTerminal C] : falsePoint C ⟶ truePoint C :=
  Arrow.leftToRight

@[simp] theorem falseToTrue_app [HasInitial C] [HasTerminal C] (a : Arrow C) :
    (falseToTrue C).app a = a.hom := rfl

/-- Each point lies over the identity on the base. -/
noncomputable def falseLift [HasTerminal C] :
    GeometricMorphism.Lift (GeometricMorphism.identity C) (projection C) where
  morphism := falsePoint C
  comparison := NatIso.ofComponents (fun _ => Iso.refl _) (by intros; exact (Category.comp_id _).trans (Category.id_comp _).symm)

/-- The true point has the same specified base leg. -/
def trueLift [HasInitial C] :
    GeometricMorphism.Lift (GeometricMorphism.identity C) (projection C) where
  morphism := truePoint C
  comparison := NatIso.ofComponents (fun _ => Iso.refl _) (by intros; exact (Category.comp_id _).trans (Category.id_comp _).symm)

/-- The false-to-true transformation respects the base comparison. -/
def falseToTrueOver [HasInitial C] [HasTerminal C] : falseLift C ⟶ trueLift C where
  transformation := falseToTrue C
  over := by ext X; exact Category.id_comp _

end SquareKit.Internal.ArrowGeometry

