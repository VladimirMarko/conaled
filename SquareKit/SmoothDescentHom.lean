import SquareKit.SmoothElementDescent

/-! Experimental gluing of arbitrary smooth algebra maps by scalar descent.
Smooth-operation preservation follows from the proved scalar operation laws. -/
noncomputable section
namespace SquareKit.SmoothAlgebra.PrincipalCover
open PresentedLocalization
variable {n m k : ℕ} {B : Type*} [CommRing B] [Algebra ℝ B] [Structure B]

def HomCompatible {ι : Type*} (r : Fin m → Free n) (s : ι → Presentation.Carrier r)
    (h : ∀ i, Hom B (At r (s i))) : Prop :=
  ∀ i j, Hom.comp (atLeft r (s i) (s j)) (h i)=Hom.comp (atRight r (s i) (s j)) (h j)

def mapSections {ι : Type*} (r : Fin m → Free n) (s : ι → Presentation.Carrier r)
    (h : ∀ i, Hom B (At r (s i))) (hh : HomCompatible r s h) (b : B) : AtSections r s :=
  ⟨fun i => h i b,fun i j => congrArg (fun f : Hom B (At r (s i*s j)) => f b) (hh i j)⟩

def glueHom (r : Fin m → Free n) (s : Fin k → Presentation.Carrier r) (hs : Covers s)
    (h : ∀ i, Hom B (At r (s i))) (hh : HomCompatible r s h) : Hom B (Presentation.Carrier r) where
  toFun b := (atDescentEquiv r s hs).symm (mapSections r s h hh b)
  map_act f b := by
    have he : mapSections r s h hh (act f b) = atSectionAct r s f (fun j => mapSections r s h hh (b j)) := by
      apply Subtype.ext
      funext i
      exact (h i).map_act f b
    rw [he,at_glue_act]

theorem glueHom_factor (r : Fin m → Free n) (s : Fin k → Presentation.Carrier r) (hs : Covers s)
    (h : ∀ i, Hom B (At r (s i))) (hh : HomCompatible r s h) (i : Fin k) :
    Hom.comp (atBase r (s i)) (glueHom r s hs h hh)=h i :=
  Hom.ext (fun b => at_glue_spec r s hs (mapSections r s h hh b) i)

theorem glueHom_unique (r : Fin m → Free n) (s : Fin k → Presentation.Carrier r) (hs : Covers s)
    (h : ∀ i, Hom B (At r (s i))) (hh : HomCompatible r s h)
    (g : Hom B (Presentation.Carrier r)) (hg : ∀ i, Hom.comp (atBase r (s i)) g=h i) :
    g=glueHom r s hs h hh := by
  apply Hom.ext
  intro b
  apply at_separated r s hs
  intro i
  exact (congrArg (fun f : Hom B (At r (s i)) => f b) (hg i)).trans
    (at_glue_spec r s hs (mapSections r s h hh b) i).symm

end SquareKit.SmoothAlgebra.PrincipalCover
