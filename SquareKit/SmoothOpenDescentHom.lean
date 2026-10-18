import SquareKit.SmoothOpenDescentOperations
import SquareKit.SmoothDescentHom

/-! Experimental arbitrary-cover descent for all smooth algebra maps. -/
noncomputable section
namespace SquareKit.SmoothAlgebra.OpenCover
open PresentedLocalization PrincipalCover
variable {n m : ℕ} {ι : Type*} {B : Type*} [CommRing B] [Algebra ℝ B] [Structure B]

def glueHom (r : Fin m → Free n) (s : ι → Presentation.Carrier r) (hs : Covers s)
    (h : ∀ i, Hom B (At r (s i))) (hh : HomCompatible r s h) : Hom B (Presentation.Carrier r) where
  toFun b := (atDescentEquiv r s hs).symm (mapSections r s h hh b)
  map_act f b := by
    have he : mapSections r s h hh (act f b) = atSectionAct r s f (fun j => mapSections r s h hh (b j)) := by
      apply Subtype.ext
      funext i
      exact (h i).map_act f b
    rw [he,at_glue_act]

theorem glueHom_factor (r : Fin m → Free n) (s : ι → Presentation.Carrier r) (hs : Covers s)
    (h : ∀ i, Hom B (At r (s i))) (hh : HomCompatible r s h) (i : ι) :
    Hom.comp (atBase r (s i)) (glueHom r s hs h hh)=h i :=
  Hom.ext (fun b => at_glue_spec r s hs (mapSections r s h hh b) i)

theorem glueHom_unique (r : Fin m → Free n) (s : ι → Presentation.Carrier r) (hs : Covers s)
    (h : ∀ i, Hom B (At r (s i))) (hh : HomCompatible r s h)
    (g : Hom B (Presentation.Carrier r)) (hg : ∀ i, Hom.comp (atBase r (s i)) g=h i) :
    g=glueHom r s hs h hh := by
  apply Hom.ext
  intro b
  apply at_separated r s hs
  intro i
  exact (congrArg (fun f : Hom B (At r (s i)) => f b) (hg i)).trans
    (at_glue_spec r s hs (mapSections r s h hh b) i).symm

end SquareKit.SmoothAlgebra.OpenCover
