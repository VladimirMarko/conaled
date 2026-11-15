import SquareKit.SmoothQuotientDescentSections
import SquareKit.Internal.PathTransport.SectionBaseEquivalence

/-! Fixed-cover reconstruction on the actual quotient-object context. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SquareKit.SmoothQuotientDeformations
open CategoryTheory CategoryTheory.Functor SheafActionQuotient SmoothOpenSite
open Internal.PathTransport.GroupoidModel
variable {H : Type} [Group H] {M X : Sheaf topology Type}
variable {a : Action (locallyConstantGroup H) M} {A : SplitSheaf.Ty X}
variable [Presheaf.IsLocallySurjective topology (SplitSheaf.p A).hom]

/-- The established deformation comparison on total families. -/
def CocycleDatum.sectionTotal :
    Extend (setFamily (Descent.descentFunctor a A ⋙ family a X)) ⥤
      Extend (setFamily (fiberFamily (a := a) (A := A))) :=
  (SectionDescent.totalEquivalence (hβ := sectionEquivalences)
    (B := setFamily (fiberFamily (a := a) (A := A)))
    CategoryTheory.Equivalence.refl (sectionComparison (a := a) (A := A))).functor

/-- Reconstruct on all quotient objects from a complete section of matching
local deformations on the fixed-cover cocycle groupoid. -/
def CocycleDatum.globalSection
    (s : Section (setFamily (fiberFamily (a := a) (A := A)))) :
    Section (setFamily (family a X)) :=
  SectionDescent.extendBase (Descent.quotientDescentEquivalence a A)
    (setFamily (family a X)) (descendSection s)

/-- Reindexing the reconstructed section and applying the actual fiber gluing
comparison recovers the entire local section, including its maps. -/
def CocycleDatum.globalSectionRecovery
    (s : Section (setFamily (fiberFamily (a := a) (A := A)))) :
    ((globalSection s).reindex (Descent.descentFunctor a A)).lift ⋙
        sectionTotal (a := a) (A := A) ≅ s.lift :=
  isoWhiskerRight
    (SectionDescent.restrictRecovery (Descent.quotientDescentEquivalence a A)
      (setFamily (family a X)) (descendSection s)) _ ≪≫
    descendSectionRecovery s

/-- The recovery does not change the selected cocycle context by an
uncontrolled automorphism. -/
theorem CocycleDatum.globalSectionRecovery_base
    (s : Section (setFamily (fiberFamily (a := a) (A := A))))
    (d : Descent.Datum (a := a) A) :
    ((globalSectionRecovery s).hom.app d).base = 𝟙 d := by
  simp only [globalSectionRecovery, Iso.trans_hom, NatTrans.comp_app,
    isoWhiskerRight_hom, whiskerRight_app, Grothendieck.comp_base]
  change ((SectionDescent.restrictRecovery (Descent.quotientDescentEquivalence a A)
    (setFamily (family a X)) (descendSection s)).hom.app d).base ≫
    ((descendSectionRecovery s).hom.app d).base = _
  rw [SectionDescent.restrictRecovery_base, descendSectionRecovery_base]
  exact Category.id_comp _

/-- On deformation objects, recovery is the original gluing equivalence,
not merely an unspecified isomorphism between endpoints. -/
theorem CocycleDatum.globalSection_recoverFiber
    (s : Section (setFamily (fiberFamily (a := a) (A := A))))
    (d : Descent.Datum (a := a) A) :
    fiberEquivalence d (((globalSection s).obj d.object).as) = (s.obj d).as := by
  have h : fiberFamily.map ((globalSectionRecovery s).hom.app d).base
      (fiberEquivalence d (((globalSection s).obj d.object).as)) = (s.obj d).as :=
    Discrete.eq_of_hom
      (X := Discrete.mk (fiberFamily.map ((globalSectionRecovery s).hom.app d).base
        (fiberEquivalence d (((globalSection s).obj d.object).as))))
      (Y := s.obj d) ((globalSectionRecovery s).hom.app d).fiber
  let v := fiberEquivalence d (((globalSection s).obj d.object).as)
  have hid : fiberFamily.map (𝟙 d) v = v :=
    congrArg (fun f : Fiber d ⟶ Fiber d => f v) (fiberFamily.map_id d)
  have hb := congrArg (fun f : d ⟶ d => fiberFamily.map f v)
    (globalSectionRecovery_base s d)
  exact hid.symm.trans (hb.symm.trans h)

/-- Recovery commutes with every compatible local arrow, not just with the
object assignment of the supplied section. -/
theorem CocycleDatum.globalSectionRecovery_naturality
    (s : Section (setFamily (fiberFamily (a := a) (A := A))))
    {d e : Descent.Datum (a := a) A} (f : d ⟶ e) :
    (sectionTotal (a := a) (A := A)).map
        (((globalSection s).reindex (Descent.descentFunctor a A)).lift.map f) ≫
          (globalSectionRecovery s).hom.app e =
      (globalSectionRecovery s).hom.app d ≫ s.lift.map f :=
  (globalSectionRecovery s).hom.naturality f

end SquareKit.SmoothQuotientDeformations
