import SquareKit.Internal.PathTransport.ComparisonJSubstitution

/-! Universe lifting is outside the small comparison model. It preserves the
chosen functor and component functions; it does not replace them by equivalences. -/
noncomputable section
namespace SquareKit.Internal.PathTransport.GroupoidModel.Comparison
open CategoryTheory
universe u₁ v₁ u₂ v₂ w
variable {C : Type u₁} [Groupoid.{v₁} C] {D : Type u₂} [Groupoid.{v₂} D]
    (R : C ⥤ D) (B : C ⥤ Type w) (E : D ⥤ Type w) (α : B ⟶ R ⋙ E)

/-- Lift independently sized endpoint groupoids and their set families to a
common universe. The family map can be noninvertible. -/
def universeSignature : Signature.{max u₁ v₁ u₂ v₂ w} where
  base := {
    left := Grpd.of (AsSmall.{max u₂ v₂ w} C)
    right := Grpd.of (AsSmall.{max u₁ v₁ w} D)
    map := AsSmall.down ⋙ R ⋙ AsSmall.up }
  leftFiber := AsSmall.down ⋙ B ⋙ uliftFunctor.{max u₁ v₁ u₂ v₂}
  rightFiber := AsSmall.down ⋙ E ⋙ uliftFunctor.{max u₁ v₁ u₂ v₂}
  fiberMap := {
    app c := ↾(fun b => ⟨α.app (ULift.down c) b.down⟩)
    naturality := by
      intro c d f
      apply ConcreteCategory.hom_ext
      intro b
      apply ULift.ext
      exact ConcreteCategory.congr_hom (α.naturality f.down) b.down }

def universeModel : Typed.Model.{max u₁ v₁ u₂ v₂ w + 1} :=
  fullModel (universeSignature R B E α)

@[simp] theorem universeSignature_arrow {c d : C} (f : c ⟶ d) :
    ((universeSignature R B E α).base.map.map
      (AsSmall.up.map f)).down = R.map f := rfl

@[simp] theorem universeSignature_fiber (c : C) (b : B.obj c) :
    ((universeSignature R B E α).fiberMap.app ⟨c⟩ ⟨b⟩).down = α.app c b := rfl

/-- When endpoint sizes agree, use precisely the existing direct-model lifts.
This preserves the direct interpretations definitionally, avoiding replacement
by an equivalent but differently lifted category. -/
def alignedUniverseSignature {C D : Type u₁} [Groupoid.{v₁} C] [Groupoid.{v₁} D]
    (R : C ⥤ D) (B : C ⥤ Type w) (E : D ⥤ Type w) (α : B ⟶ R ⋙ E) :
    Signature.{max u₁ v₁ w} where
  base := {
    left := Grpd.of (AsSmall.{w} C)
    right := Grpd.of (AsSmall.{w} D)
    map := AsSmall.down ⋙ R ⋙ AsSmall.up }
  leftFiber := Instance.liftedFamily C B
  rightFiber := Instance.liftedFamily D E
  fiberMap := {
    app c := ↾(fun b => ⟨α.app (ULift.down c) b.down⟩)
    naturality := by
      intro c d f
      apply ConcreteCategory.hom_ext
      intro b
      apply ULift.ext
      exact ConcreteCategory.congr_hom (α.naturality f.down) b.down }

end SquareKit.Internal.PathTransport.GroupoidModel.Comparison
