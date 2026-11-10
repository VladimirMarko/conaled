import SquareKit.SmoothQuotientCechFibers
import SquareKit.SheafActionQuotientDescentBaseChange
import Examples.LocalDeformationSections

/-! Independent matching data recover pointwise cocycles without discarding
selected arrows. Effectivity is used only by the final global comparison. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Examples.CechDeformationDescent
open CategoryTheory SquareKit SheafActionQuotient SmoothOpenSite
open SmoothQuotientDeformations
variable {H : Type} [Group H] {M X : Sheaf topology Type}
variable {a : Action (locallyConstantGroup H) M} {A : SplitSheaf.Ty X}

/-- An independently supplied overlap isomorphism is recovered, including its
inverse, after extraction and reconstruction of pointwise transport. -/
example (d : SheafActionQuotient.Cech.Datum (a := a) A) :
    SheafActionQuotient.Cech.ofDescent d.toDescent = d :=
  SheafActionQuotient.Cech.ofDescent_toDescent d

/-- The deformation comparison recovers the exact local deformation. -/
example (d : SheafActionQuotient.Cech.Datum (a := a) A)
    (h : SmoothQuotientDeformations.Cech.Fiber d) :
    ((SmoothQuotientDeformations.Cech.fiberEquiv d).symm
      (SmoothQuotientDeformations.Cech.fiberEquiv d h)).val = h.val :=
  congrArg Subtype.val ((SmoothQuotientDeformations.Cech.fiberEquiv d).symm_apply_apply h)

/-- Constant deformation gives an actual matching fiber for every local
cocycle, including nontrivial torsors and ineffective actions. -/
def constantMatching (d : Descent.Datum (a := a) A) :
    SmoothQuotientDeformations.Cech.Fiber (SheafActionQuotient.Cech.ofDescent d) :=
  (SmoothQuotientDeformations.Cech.fiberEquiv _).symm
    ⟨constant d.localObject, fun x b c _ p => d.value_compatible x b c p⟩

/-- The forward comparison retains the selected overlap, not just endpoints. -/
example (d : Descent.Datum (a := a) A) :
    (SheafActionQuotient.Cech.ofDescent d).overlap.hom = d.overlapArrow := rfl

/-- A nonidentity global loop cannot be used as a constant matching overlap:
its diagonal already fails. This uses a real quotient arrow, not a Boolean
approximation to an overlap isomorphism. -/
theorem rejects_constant_loop
    [Presheaf.IsLocallySurjective topology (SplitSheaf.p A).hom]
    (P : Object a X) (k : P ⟶ P) (hk : k ≠ 𝟙 P) :
    (k.reindex (SplitSheaf.Cech.first A ≫ SplitSheaf.p A)).reindex
      (SplitSheaf.Cech.diagonal A) ≠
      Arrow.ident (reindex P (SplitSheaf.p A)) := by
  intro he
  apply hk
  apply Descent.restriction_injective (A := A)
  exact he

variable (K : Type) [Group K] (c : K) (B : SplitSheaf.Ty SmoothClutching.base)

/-- This actual instance retains the doubled-origin torsor; c ≠ 1 rules out
any global chart, as proved by the existing consumer. -/
def nontrivialMatching :
    SmoothQuotientDeformations.Cech.Fiber (SheafActionQuotient.Cech.ofDescent
      (Descent.canonicalDatum B (ActionQuotientEvidence.nontrivialObject K c))) :=
  constantMatching _

/-- Distinct selected loops survive the forward identification on this
ineffective quotient object. -/
example [Presheaf.IsLocallySurjective topology (SplitSheaf.p B).hom]
    (p q : ActionQuotientEvidence.nontrivialObject K c ⟶
      ActionQuotientEvidence.nontrivialObject K c) (hpq : p ≠ q) :
    SheafActionQuotient.Cech.fromDescent.map
        ((Descent.canonicalArrowEquiv B _ _).symm p) ≠
      SheafActionQuotient.Cech.fromDescent.map
        ((Descent.canonicalArrowEquiv B _ _).symm q) := by
  intro he
  apply hpq
  apply (Descent.canonicalArrowEquiv B _ _).symm.injective
  exact (SheafActionQuotient.Cech.equivalence.inverse.map_injective he)

end Examples.CechDeformationDescent
