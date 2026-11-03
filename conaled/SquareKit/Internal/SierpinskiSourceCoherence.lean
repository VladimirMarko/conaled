import SquareKit.Internal.SierpinskiSourceChange
import SquareKit.Internal.GeometricLiftCoherence

/-! Unit, composition, and transformation diagrams for source substitution.
The equations live in the actual model categories, with all comparison maps. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SquareKit.Internal.Sierpinski
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
universe vF vG vH vB uF uG uH uB
variable {F : Type uF} {G : Type uG} {H : Type uH} {B : Type uB}
variable [Category.{vF} F] [Category.{vG} G] [Category.{vH} H] [Category.{vB} B]
variable [HasFiniteLimits F] [HasFiniteLimits G] [HasFiniteLimits H]
variable [HasInitial B] [HasFiniteLimits B] [HasStrictInitialObjects B]
variable {h h' : GeometricMorphism F B}

/-- Rebasing only changes the comparison, so the actual generic carrier is unchanged. -/
def rebaseComparison (e : h.inverseImage ≅ h'.inverseImage) :
    GeometricMorphism.Lift.rebaseFunctor (π := ArrowGeometry.projection B) e ⋙ liftInterpretation h' ≅
      liftInterpretation h :=
  NatIso.ofComponents (fun _ => MonoOver.isoMk (Iso.refl _) (terminal.hom_ext _ _))
    (by intros; apply Subsingleton.elim)

/-- The identity source-comparison triangle commutes after the required rebase. -/
theorem source_identity (k : GeometricMorphism.Lift h (ArrowGeometry.projection B)) :
    (liftInterpretation h).map (GeometricMorphism.Lift.sourceIdentityIso.hom.app k) =
      (rebaseComparison (h := (GeometricMorphism.identity F).comp h) (h' := h)
        (Functor.rightUnitor h.inverseImage)).hom.app
        (k.precomp (GeometricMorphism.identity F)) ≫
      (sourceComparison h (GeometricMorphism.identity F)).hom.app k ≫
        SubterminalChange.identity.hom.app ((liftInterpretation h).obj k) :=
  Subsingleton.elim _ _

/-- Successive source comparisons agree with the composite comparison and associator. -/
theorem source_comp (f : GeometricMorphism G F) (g : GeometricMorphism H G)
    (k : GeometricMorphism.Lift h (ArrowGeometry.projection B)) :
    (liftInterpretation ((g.comp f).comp h)).map
        ((GeometricMorphism.Lift.sourceCompIso f g).hom.app k) ≫
      (sourceComparison h (g.comp f)).hom.app k =
    (rebaseComparison (h := g.comp (f.comp h)) (h' := (g.comp f).comp h)
        (Functor.associator h.inverseImage f.inverseImage g.inverseImage)).hom.app
        ((k.precomp f).precomp g) ≫
      (sourceComparison (f.comp h) g).hom.app (k.precomp f) ≫
      (SubterminalChange.pull g).map ((sourceComparison h f).hom.app k) ≫
      (SubterminalChange.comp f g).hom.app ((liftInterpretation h).obj k) :=
  Subsingleton.elim _ _

/-- The geometric source 2-cell and the model source 2-cell form the same square. -/
theorem source_transformation {f g : GeometricMorphism G F} (α : f ⟶ g)
    (k : GeometricMorphism.Lift h (ArrowGeometry.projection B)) :
    interpretation.map (show (f.comp k.morphism) ⟶ (g.comp k.morphism) from
      whiskerLeft k.morphism.inverseImage α) ≫ (sourceComparison h g).hom.app k =
      (sourceComparison h f).hom.app k ≫ (sourceTransformation h α).app k :=
  Subsingleton.elim _ _

end SquareKit.Internal.Sierpinski
