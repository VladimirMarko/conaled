import SquareKit.SmoothQuotientGlobalSections
import Examples.SmoothDescentMaps
import Examples.SectionDescent

/-! Global section reconstruction retains arbitrary torsors and selected arrows. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Examples.GlobalSectionDescent
open CategoryTheory SquareKit SheafActionQuotient SmoothOpenSite
open SmoothQuotientDeformations Internal.PathTransport.GroupoidModel
variable {H : Type} [Group H] {M X : Sheaf topology Type}
variable {a : Action (locallyConstantGroup H) M} {A : SplitSheaf.Ty X}
variable [Presheaf.IsLocallySurjective topology (SplitSheaf.p A).hom]

/-- Constant deformations supply a usable complete local section without
requiring a trivialization of any torsor. -/
theorem transport_constant {P Q : Object a X} (f : P ⟶ Q) :
    transport f (SmoothQuotientDeformations.constant P) =
      SmoothQuotientDeformations.constant Q := by
  apply Deformation.ext
  ext U p
  exact (Arrow.inverse f).preserves (X.obj.elementsMk U p.2.1) p.2.2

private def setSection {Γ : Type*} [Category* Γ] (F : Γ ⥤ Type*)
    (x : ∀ γ, F.obj γ) (hx : ∀ {γ δ} (f : γ ⟶ δ), F.map f (x γ) = x δ) :
    Section (setFamily F) where
  obj γ := Discrete.mk (x γ)
  map f := eqToHom (congrArg Discrete.mk (hx f))
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

def constantLocal : Section (setFamily (CocycleDatum.fiberFamily (a := a) (A := A))) :=
  setSection _
    (fun d => CocycleDatum.fiberEquivalence d (SmoothQuotientDeformations.constant d.object))
    (by
      intro d e f
      change CocycleDatum.fiberEquivalence e
        (transport f.arrow ((CocycleDatum.fiberEquivalence d).symm
          (CocycleDatum.fiberEquivalence d (SmoothQuotientDeformations.constant d.object)))) = _
      exact (congrArg (fun z => CocycleDatum.fiberEquivalence e (transport f.arrow z))
        ((CocycleDatum.fiberEquivalence d).symm_apply_apply _)).trans
          (congrArg (CocycleDatum.fiberEquivalence e) (transport_constant f.arrow)))

/-- This is an actual global section, not an additional assumption. -/
def reconstructedConstant : Section (setFamily (family a X)) :=
  CocycleDatum.globalSection (constantLocal (a := a) (A := A))

/-- The public recovery theorem computes the reconstructed deformation at a
descended quotient object, using the original gluing equivalence. -/
theorem reconstructedConstant_on_descended (d : Descent.Datum (a := a) A) :
    ((reconstructedConstant (a := a) (A := A)).obj d.object).as =
      SmoothQuotientDeformations.constant d.object :=
  (CocycleDatum.fiberEquivalence d).injective
    (CocycleDatum.globalSection_recoverFiber (constantLocal (a := a) (A := A)) d)

variable (H : Type) [Group H] (c : H) (A : SplitSheaf.Ty SmoothClutching.base)
variable [Presheaf.IsLocallySurjective topology (SplitSheaf.p A).hom]

/-- The global construction has a component at the nontrivial doubled-origin
torsor itself, with no chart choice or effectiveness assumption. -/
example : Deformation (ActionQuotientEvidence.nontrivialObject H c) :=
  ((reconstructedConstant (a := ActionQuotientEvidence.ineffective H) (A := A)).obj
    (ActionQuotientEvidence.nontrivialObject H c)).as

/-- Its lift retains every selected loop of that quotient object. -/
example (p q : ActionQuotientEvidence.nontrivialObject H c ⟶
    ActionQuotientEvidence.nontrivialObject H c) (hpq : p ≠ q) :
    (reconstructedConstant (a := ActionQuotientEvidence.ineffective H) (A := A)).lift.map p ≠
      (reconstructedConstant (a := ActionQuotientEvidence.ineffective H) (A := A)).lift.map q := by
  intro h
  exact hpq (congrArg Grothendieck.Hom.base h)

/-- Recovery at the cocycle presentation is vertical, including for this
nontrivial-torsor specialization. -/
example :
    ((CocycleDatum.globalSectionRecovery
      (constantLocal (a := ActionQuotientEvidence.ineffective H) (A := A))).hom.app
        (Descent.canonicalDatum A (ActionQuotientEvidence.nontrivialObject H c))).base =
      𝟙 (Descent.canonicalDatum A (ActionQuotientEvidence.nontrivialObject H c)) :=
  CocycleDatum.globalSectionRecovery_base _ _

end Examples.GlobalSectionDescent
