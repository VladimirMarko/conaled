import SquareKit.SheafActionQuotientDescentBaseChange
import Examples.SmoothDescentMaps

/-! Parameter change preserves the chosen descent comparison, including its
arrow action. Restriction need not preserve distinctions at arbitrary parameters. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Examples.QuotientDescentBaseChange
open CategoryTheory SquareKit SheafActionQuotient SmoothOpenSite

/-- Arbitrary local cocycles recover their original comparison on the pulled-back
cover. No global object is supplied as an input. -/
example {H : Type} [Group H] {M X Y : Sheaf topology Type}
    {a : Action (locallyConstantGroup H) M} {A : SplitSheaf.Ty X}
    [Presheaf.IsLocallySurjective topology (SplitSheaf.p A).hom]
    (d : Descent.Datum (a := a) A) (f : Y ⟶ X) :
    ((d.baseChangeComparison f).reindex (SplitSheaf.p (SplitSheaf.tySub A f))).comp
      (d.baseChange f).comparison = d.comparison.reindex (SplitSheaf.lift A f) :=
  d.baseChangeComparison_recover f

variable (H : Type) [Group H] (c : H) (A : SplitSheaf.Ty SmoothClutching.base)
variable [Presheaf.IsLocallySurjective topology (SplitSheaf.p A).hom]

/-- Base change applies to the cocycle presentation of the doubled-origin torsor,
even when that torsor has no global chart. It does not assert that every
restriction remains nontrivial. -/
example {Y : Sheaf topology Type} (f : Y ⟶ SmoothClutching.base) :
    reindex (Descent.canonicalDatum A
      (ActionQuotientEvidence.nontrivialObject H c)).object f ≅
    ((Descent.canonicalDatum A
      (ActionQuotientEvidence.nontrivialObject H c)).baseChange f).object :=
  ((Descent.canonicalDatum A
    (ActionQuotientEvidence.nontrivialObject H c)).baseChangeComparison f).toIso

/-- Identity base change retains selected distinct loops on the ineffective
nontrivial torsor. Object-only comparison would not establish this. -/
example (p q : ActionQuotientEvidence.nontrivialObject H c ⟶
    ActionQuotientEvidence.nontrivialObject H c) (hpq : p ≠ q) :
    (Descent.baseChange (A := A) (𝟙 SmoothClutching.base)).map
        ((Descent.canonicalArrowEquiv A _ _).symm p) ≠
      (Descent.baseChange (A := A) (𝟙 SmoothClutching.base)).map
        ((Descent.canonicalArrowEquiv A _ _).symm q) := by
  rw [Descent.baseChange_id]
  exact fun h => hpq ((Descent.canonicalArrowEquiv A _ _).symm.injective h)

end Examples.QuotientDescentBaseChange
