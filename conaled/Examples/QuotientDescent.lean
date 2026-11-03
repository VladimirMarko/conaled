import SquareKit.SheafActionQuotientDescent
import SquareKit.SmoothClutchingPrincipal
noncomputable section
open CategoryTheory
open SquareKit
namespace ActionQuotientEvidence
variable (G : Type) [Group G] (c : G)
def ineffective : SheafActionQuotient.Action
    (SmoothOpenSite.locallyConstantGroup G) SmoothClutching.base where
  act _ _ x := x
  one_act _ _ := rfl
  mul_act _ _ _ _ := rfl
  natural _ _ _ := rfl

def nontrivialObject := SheafActionQuotient.invariantObject (a := ineffective G)
  (SmoothClutching.torsor G c) (𝟙 SmoothClutching.base) (fun _ _ => rfl)

example (hc : c ≠ 1) (m : SmoothClutching.base ⟶ SmoothClutching.base) :
    ¬ Nonempty (SheafActionQuotient.Arrow
      (SheafActionQuotient.chart (ineffective G) m) (nontrivialObject G c)) :=
  SheafActionQuotient.not_chart_of_no_section (nontrivialObject G c)
    (SmoothClutching.no_global_section G c hc) m

example (m : SmoothClutching.base ⟶ SmoothClutching.base) :
    Function.Injective (fun g : SmoothClutching.base ⟶
      SheafTorsor.groupSheaf (SmoothOpenSite.locallyConstantGroup G) =>
      SheafActionQuotient.chartArrowOfRelation (a := ineffective G) g m m rfl) := by
  intro g h he
  apply SheafTorsor.regularArrow_injective
  exact congrArg SheafActionQuotient.Arrow.torsorArrow he

/-- Effective descent recovers this nontrivial quotient object over every
locally surjective split cover, without choosing a global section. -/
example (A : SplitSheaf.Ty SmoothClutching.base)
    [Presheaf.IsLocallySurjective SmoothOpenSite.topology (SplitSheaf.p A).hom] :
    SheafActionQuotient.Arrow
      (SheafActionQuotient.Descent.canonicalDatum A (nontrivialObject G c)).object
      (nontrivialObject G c) :=
  SheafActionQuotient.Descent.canonicalRecovery A (nontrivialObject G c)

example (A : SplitSheaf.Ty SmoothClutching.base)
    [Presheaf.IsLocallySurjective SmoothOpenSite.topology (SplitSheaf.p A).hom] :
    SheafActionQuotient.Descent.Map
      (SheafActionQuotient.Descent.canonicalDatum A (nontrivialObject G c))
      (SheafActionQuotient.Descent.canonicalDatum A (nontrivialObject G c)) ≃
      SheafActionQuotient.Arrow (nontrivialObject G c) (nontrivialObject G c) :=
  SheafActionQuotient.Descent.canonicalArrowEquiv A (nontrivialObject G c) (nontrivialObject G c)
end ActionQuotientEvidence
