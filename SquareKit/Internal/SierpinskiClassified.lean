import SquareKit.Internal.ArrowSheaf
import SquareKit.Internal.ArrowPushoutModels

/-! Construct relative Sierpiński lifts from actual subterminal sheaves and
retain every model map as a geometric transformation. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SquareKit.Internal.Sierpinski
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
universe v u vB uB
variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
variable {B : Type uB} [Category.{vB} B] [HasInitial B] [HasFiniteLimits B]
variable (h : GeometricMorphism (Sheaf J (Type (max u v))) B)

/-- The classified geometric morphism has inverse image `Arrow(h*) ⋙ K_P`. -/
def classified (P : MonoOver (⊤_ (Sheaf J (Type (max u v))))) :
    GeometricMorphism.Lift h (ArrowGeometry.projection B) where
  morphism := (ArrowSheaf.ofSubterminal J P).comp (ArrowTransport.geometric h)
  comparison :=
    (Functor.associator (ArrowGeometry.diagonal B) h.inverseImage.mapArrow
      (ArrowPushout.interpretation P.obj.left)).symm ≪≫
    isoWhiskerRight (ArrowTransport.diagonalIso h.inverseImage) (ArrowPushout.interpretation P.obj.left) ≪≫
    Functor.associator h.inverseImage (ArrowGeometry.diagonal _)
      (ArrowPushout.interpretation P.obj.left) ≪≫
    isoWhiskerLeft h.inverseImage (ArrowPushout.diagonalIso P.obj.left) ≪≫
    Functor.rightUnitor h.inverseImage

/-- Model inclusions act by the canonical pushout transformation. -/
def classify : MonoOver (⊤_ (Sheaf J (Type (max u v)))) ⥤
    GeometricMorphism.Lift h (ArrowGeometry.projection B) where
  obj := classified J h
  map {P Q} f := {
    transformation := whiskerLeft h.inverseImage.mapArrow
      (ArrowPushout.changeParameter P.obj.left f.hom.left)
    over := by
      apply NatTrans.ext
      funext X
      dsimp [classified, ArrowGeometry.projection, ArrowSheaf.ofSubterminal, ArrowSheaf.geometric, GeometricMorphism.comp, ArrowTransport.geometric]
      simp only [Category.id_comp, Category.comp_id]
      rw [← (ArrowPushout.changeParameter P.obj.left f.hom.left).naturality_assoc]
      congr 1
      exact congrArg (fun α => α.app (h.inverseImage.obj X))
        (ArrowPushout.changeParameter_over P.obj.left f.hom.left) }
  map_id P := by
    apply GeometricMorphism.Lift.Hom.ext
    change whiskerLeft h.inverseImage.mapArrow (ArrowPushout.changeParameter P.obj.left (𝟙 _)) = _
    rw [ArrowPushout.changeParameter_id]
    rfl
  map_comp {P Q R} f g := by
    apply GeometricMorphism.Lift.Hom.ext
    change whiskerLeft h.inverseImage.mapArrow
      (ArrowPushout.changeParameter P.obj.left (f.hom.left ≫ g.hom.left)) = _
    rw [ArrowPushout.changeParameter_comp]
    rfl

/-- Inverse images preserve the initial and terminal endpoints of the generic arrow. -/
def mapGeneric : h.inverseImage.mapArrow.obj (generic B) ≅
    generic (Sheaf J (Type (max u v))) :=
  Arrow.isoMk (PreservesInitial.iso h.inverseImage) (PreservesTerminal.iso h.inverseImage)
    (by apply terminal.hom_ext)

variable [HasStrictInitialObjects B]

/-- Evaluating the constructed lift recovers the actual model carrier. -/
def classifiedGenericIso (P : MonoOver (⊤_ (Sheaf J (Type (max u v))))) :
    (liftInterpretation h).obj ((classify J h).obj P) ≅ P :=
  MonoOver.isoMk
    ((ArrowPushout.interpretation P.obj.left).mapIso (mapGeneric J h) ≪≫
      ArrowPushout.genericIso P.obj.left)
    (terminal.hom_ext _ _)

/-- The generic-model comparison is natural, including noninvertible model maps. -/
def classifyInterpretation : classify J h ⋙ liftInterpretation h ≅
    𝟭 (MonoOver (⊤_ (Sheaf J (Type (max u v))))) :=
  NatIso.ofComponents (classifiedGenericIso J h) (by intros; apply Subsingleton.elim)

end SquareKit.Internal.Sierpinski
