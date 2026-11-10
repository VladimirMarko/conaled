import SquareKit.SmoothQuotientDescentExtension
import SquareKit.GrothendieckEquivalence
import Examples.QuotientDescent

/-! The descent comparisons apply to arbitrary local cocycles and retain
arrows over quotient objects with no global trivialization. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Examples.SmoothDescentMaps
open CategoryTheory SquareKit SheafActionQuotient SmoothOpenSite
open SmoothQuotientDeformations GrothendieckEquivalence

/-- The inputs are local quotient and deformation data, not restrictions of
an assumed global deformation. Their compatibility descends and reflects. -/
example {H : Type} [Group H] {M X : Sheaf topology Type}
    {a : Action (locallyConstantGroup H) M} {A : SplitSheaf.Ty X}
    [Presheaf.IsLocallySurjective topology (SplitSheaf.p A).hom]
    (d e : CocycleDatum (a := a) A) (h : Descent.Map d.quotient e.quotient) :
    transport h.arrow d.descend = e.descend ↔
      transport h.localArrow d.localDeformation = e.localDeformation :=
  d.map_descend_iff e h

/-- One context extension uses the generic theorem on actual local data. -/
example {H : Type} [Group H] {M X : Sheaf topology Type}
    {a : Action (locallyConstantGroup H) M} {A : SplitSheaf.Ty X}
    [Presheaf.IsLocallySurjective topology (SplitSheaf.p A).hom]
    (d : Descent.Datum (a := a) A) (s : CocycleDatum.Fiber d) :
    (CocycleDatum.extensionEquivalence.functor.obj ⟨d, Discrete.mk s⟩).fiber =
      Discrete.mk (CocycleDatum.ofFiber d s).descend := rfl

variable (H : Type) [Group H] (c : H) (A : SplitSheaf.Ty SmoothClutching.base)
variable [Presheaf.IsLocallySurjective topology (SplitSheaf.p A).hom]

/-- The functor of the new equivalence recovers the existing nontrivial torsor.
For c ≠ 1 it cannot be replaced by a globally trivial chart. -/
example :
    (Descent.quotientDescentEquivalence (ActionQuotientEvidence.ineffective H) A).functor.obj
      (Descent.canonicalDatum A (ActionQuotientEvidence.nontrivialObject H c)) ≅
        ActionQuotientEvidence.nontrivialObject H c :=
  (Descent.canonicalRecovery A _).toIso

/-- The reconstructed object itself still cannot have a global chart lift. -/
example (hc : c ≠ 1) (m : SmoothClutching.base ⟶ SmoothClutching.base) :
    ¬ Nonempty (Arrow (chart (ActionQuotientEvidence.ineffective H) m)
      ((Descent.quotientDescentEquivalence (ActionQuotientEvidence.ineffective H) A).functor.obj
        (Descent.canonicalDatum A (ActionQuotientEvidence.nontrivialObject H c)))) := by
  rintro ⟨h⟩
  exact not_chart_of_no_section (ActionQuotientEvidence.nontrivialObject H c)
    (SmoothClutching.no_global_section H c hc) m
    ⟨h.comp (Descent.canonicalRecovery A _)⟩

/-- All selected loops are retained, including when the action is ineffective. -/
example (p q : ActionQuotientEvidence.nontrivialObject H c ⟶
    ActionQuotientEvidence.nontrivialObject H c) (hpq : p ≠ q) :
    (Descent.canonicalArrowEquiv A _ _).symm p ≠
      (Descent.canonicalArrowEquiv A _ _).symm q :=
  fun h => hpq ((Descent.canonicalArrowEquiv A _ _).symm.injective h)

/-- Endpoint recovery in the new identity comparison retains the complete
hom type of the nontrivial quotient object. -/
def nontrivialLoopComparison :
    (Descent.canonicalDatum A (ActionQuotientEvidence.nontrivialObject H c) ⟶
      Descent.canonicalDatum A (ActionQuotientEvidence.nontrivialObject H c)) ≃
    (ActionQuotientEvidence.nontrivialObject H c ⟶ ActionQuotientEvidence.nontrivialObject H c) :=
  identityComparisonEquiv (Descent.descentFunctor (ActionQuotientEvidence.ineffective H) A)
    (Descent.canonicalRecovery A _).toIso (Descent.canonicalRecovery A _).toIso

end Examples.SmoothDescentMaps
